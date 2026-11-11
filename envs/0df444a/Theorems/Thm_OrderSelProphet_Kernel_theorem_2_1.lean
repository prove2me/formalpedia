-- Prove2me | Theorems.Thm_OrderSelProphet_Kernel_theorem_2_1
-- name    : OrderSelProphet.Kernel.theorem_2_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:56:25.50168+00:00
-- url     : https://prove2.me/theorems/82c5d0e2-7d64-4938-baf3-0c386ae28fa6
-- title:
--   Theorem 2.1 — the arrival construction: qualifying arrivals, $P(\text{no acceptance by }t)=1-\Gamma t$, $P(I=i,\,T_i\le t)=\Gamma B_i(t)$, and the exact item-wise guarantee (1)
-- statement:
--   Let $\Gamma\in(0,1)$ and let $F_1,\dots,F_n$ be an atomless input of independent nonnegative values. Suppose the allocation functions $B_i$ satisfy (4) and the loads satisfy $L_i=L_\Gamma(A_i,B_i)\le1$ for every item. Run the algorithm with arrival laws (5) (arrival times independent of each other and of the values) and thresholds $y_i=A_i^{\leftarrow}\circ B_i$. Then for every item $i$ and every $t\in[0,1]$:
--
--   - $P\big(T_i\in(0,t],\ U_i\le y_i(T_i)\big)=1-S_i(t)$;
--   - $P(\text{no item is accepted by time }t)=1-\Gamma t$;
--   - $P(\text{item }i\text{ is accepted by time }t)=\Gamma B_i(t)$;
--   - the exact item-wise guarantee (1) holds: $P(I=i,\ V_i\in E)=\Gamma\int_E\prod_{j\ne i}F_j\,dF_i$ for every Borel $E$.
--
--   Differences from the source:
--   - generalization: inputs with n ≥ 2 items (§2, p. 6: 'The case n = 1 is immediate, so we assume n ≥ 2') → every input with n ≥ 1 items (IsInput requires 0 < n); reason: every n ≥ 2 input is included, so the statement specializes to the source's; the n = 1 case is the 'immediate' one
--   - encoding: the item-wise guarantee (1): P(I = i | V_i = v) = Γ ∏_{j≠i} F_j(v) for F_i-a.e. v → ItemwiseGuarantee: P(I = i, V_i ∈ E) = Γ ∫_E ∏_{j≠i} F_j dF_i for every Borel E; reason: the integrated form is the definition of the conditional probability; it holds for all Borel E iff the a.e. identity holds
--   - encoding: the arrival-time algorithm of §2.1: T_i ~ G_i on [0,1] ∪ {†} independent of each other and of the values; inspect in arrival order with a fixed tie rule; accept the first item with U_i ≤ y_i(T_i); I = † and ALG = 0 if none → a probability space with V_i, T_i measurable, P.map V_i = F_i, P.map T_i = G_i, the 2n σ-algebras mutually independent (iIndep); † = ⊤ in WithTop ℝ; I = runIndex (first passing item in the order (T_i, i)), none for †; ALG = algValue; reason: the fixed tie rule is 'smaller index first'; each item's test reads only its own (T_i, V_i) and the known laws
--   - encoding: loads ℓ_Γ(K,λ), L_i ∈ [0,∞) → loads in ℝ≥0∞ (loadL; ⊤ only when the allocation or threshold is not nondecreasing on [0,1], which never happens for kernel allocations); reason: loads are nonnegative Stieltjes integrals; ℝ≥0∞ avoids Bochner junk values
--   - encoding: 'item i is accepted by time t' and 'no item is accepted by time t' → I = some i with T_i = s ≤ t; and the complement of '∃ j, I = some j with T_j = s ≤ t'; reason: an accepted item has a real arrival time in (0,1]; probabilities are compared in ℝ≥0∞ via ENNReal.ofReal
-- source:
--   Peng and Tang, Order-selection Prophet Inequality (Almost) Goes I.I.D., arXiv:2610.34892 (held file SHA-256 2f111b85…22dd), Theorem 2.1, p. 8 (proof in Appendix A.3, pp. 37–38)

import Mathlib
import Definitions.Def_OrderSelProphet_Kernel_Model

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace OrderSelProphet.Kernel

/-- Theorem 2.1, p. 8 (proof in Appendix A.3, pp. 37–38): the arrival construction (5) with
allocation functions satisfying (4) and all loads at most one. -/
theorem theorem_2_1 {Γ : ℝ} (hΓ : Γ ∈ Ioo (0 : ℝ) 1) {n : ℕ} (F : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (F i)] (hF : IsAtomlessInput F) (B : Fin n → ℝ → ℝ)
    (hB : IsAllocation F B) (hL : ∀ i, loadL Γ (inputArea F i) (B i) ≤ 1)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (V : Fin n → Ω → ℝ)
    (T : Fin n → Ω → WithTop ℝ)
    (hrun : IsArrivalRun P V T F (fun i => arrivalLaw Γ (inputArea F i) (B i))) :
    let y : Fin n → ℝ → ℝ := fun i => threshold (inputArea F i) (B i)
    let I : Ω → Option (Fin n) := fun ω => runIndex F y (fun j => T j ω) (fun j => V j ω)
    (∀ i, ∀ t ∈ Icc (0 : ℝ) 1,
        P {ω | ∃ s : ℝ, T i ω = (s : WithTop ℝ) ∧ s ∈ Ioc 0 t ∧ lossScore F i (V i ω) ≤ y i s} =
          ENNReal.ofReal (1 - itemSurvival Γ (B i) t)) ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        P {ω | ¬ ∃ j, ∃ s : ℝ, I ω = some j ∧ T j ω = (s : WithTop ℝ) ∧ s ≤ t} =
          ENNReal.ofReal (1 - Γ * t)) ∧
      (∀ i, ∀ t ∈ Icc (0 : ℝ) 1,
        P {ω | I ω = some i ∧ ∃ s : ℝ, T i ω = (s : WithTop ℝ) ∧ s ≤ t} =
          ENNReal.ofReal (Γ * B i t)) ∧
      ItemwiseGuarantee Γ F P V I := by sorry

end OrderSelProphet.Kernel
