-- Prove2me | Theorems.Thm_OrderSelProphet_Kernel_proposition_4_1
-- name    : OrderSelProphet.Kernel.proposition_4_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:57:58.958362+00:00
-- url     : https://prove2.me/theorems/7c905c27-b80f-4907-8e33-9726f5584c38
-- title:
--   Proposition 4.1 — universal feasibility: feasible on every atomless input iff $\sup_\lambda\ell_\Gamma(K,\lambda)\le1$; then (1) holds, and the guarantee extends to inputs with atoms
-- statement:
--   Fix $\Gamma\in(0,1)$ and an allocation kernel $K$. The prescribed arrival construction is feasible for every atomless input (every item's load $L_i\le1$) if and only if
--   $$\sup_{\lambda\in\Lambda}\ell_\Gamma(K,\lambda)\le1.\quad(21)$$
--   Whenever (21) holds, the resulting algorithm satisfies the exact item-wise guarantee (1) for every atomless input. Moreover, the same competitive guarantee extends to arbitrary independent nonnegative distributions, including those with atoms: the construction run on the tie-broken scores of Appendix H satisfies $\mathbb E[\mathrm{ALG}]\ge\Gamma\,\mathbb E[\mathrm{OPT}]$.
--
--   Differences from the source:
--   - generalization: inputs with n ≥ 2 items (§2, p. 6: 'The case n = 1 is immediate, so we assume n ≥ 2') → every input with n ≥ 1 items (IsInput requires 0 < n); reason: every n ≥ 2 input is included, so the statement specializes to the source's; the n = 1 case is the 'immediate' one
--   - encoding: loads ℓ_Γ(K,λ), L_i ∈ [0,∞) → loads in ℝ≥0∞ (loadL; ⊤ only when the allocation or threshold is not nondecreasing on [0,1], which never happens for kernel allocations); reason: loads are nonnegative Stieltjes integrals; ℝ≥0∞ avoids Bochner junk values
--   - encoding: sup_{λ∈Λ} ℓ_Γ(K,λ) ≤ 1 → ⨆ over Profile of loadK Γ K λ in ℝ≥0∞, ≤ 1; reason: the supremum of a family of [0,∞]-valued loads; no junk value
--   - encoding: B_i(t) = B_{K,λ_i}(t) = ∫_0^1 λ_i(u) K(t,u) du with λ_i the profile (10) of item i → inputAlloc K F i t = E[1{I* = i} K(t, U)] with U = 1 − F_max(V_i) on {I* = i}; reason: equal by (10); this avoids choosing a version of λ_i
--   - encoding: the item-wise guarantee (1): P(I = i | V_i = v) = Γ ∏_{j≠i} F_j(v) for F_i-a.e. v → ItemwiseGuarantee: P(I = i, V_i ∈ E) = Γ ∫_E ∏_{j≠i} F_j dF_i for every Borel E; reason: the integrated form is the definition of the conditional probability; it holds for all Borel E iff the a.e. identity holds
--   - encoding: the arrival-time algorithm of §2.1: T_i ~ G_i on [0,1] ∪ {†} independent of each other and of the values; inspect in arrival order with a fixed tie rule; accept the first item with U_i ≤ y_i(T_i); I = † and ALG = 0 if none → a probability space with V_i, T_i measurable, P.map V_i = F_i, P.map T_i = G_i, the 2n σ-algebras mutually independent (iIndep); † = ⊤ in WithTop ℝ; I = runIndex (first passing item in the order (T_i, i)), none for †; ALG = algValue; reason: the fixed tie rule is 'smaller index first'; each item's test reads only its own (T_i, V_i) and the known laws
--   - encoding: Appendix H: the construction with kernel K run on the scores X_i = F_mix(V_i^-) + Z_i(F_mix(V_i) − F_mix(V_i^-)), Z_i i.i.d. U[0,1] independent of the values → IsScoreRun: V_i ~ F_i, Z_i ~ U[0,1], T_i ~ the arrival laws of the kernel construction on the score laws (scoreLaw), the 3n σ-algebras mutually independent; I = scoreIndex (tests on the realized scores), ALG = V_I; reason: exactly the construction of Appendix H; item i's test reads only (T_i, V_i, Z_i)
--   - generalization: E[ALG] ≥ Γ E[OPT] (with E[ALG] = Γ E[OPT] 'whenever E[OPT] < ∞', p. 75) → Γ ∫⁻ max_i V_i dP ≤ ∫⁻ ALG dP in ℝ≥0∞; reason: covers E[OPT] = ∞ as well; for E[OPT] < ∞ it is the source's inequality
-- source:
--   Peng and Tang, Order-selection Prophet Inequality (Almost) Goes I.I.D., arXiv:2610.34892 (held file SHA-256 2f111b85…22dd), Proposition 4.1, p. 13; Appendix H, p. 75

import Mathlib
import Definitions.Def_OrderSelProphet_Kernel_Scores

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace OrderSelProphet.Kernel

/-- Proposition 4.1 (Universal feasibility), p. 13, with the extension of Appendix H, p. 75. -/
theorem proposition_4_1 {Γ : ℝ} (hΓ : Γ ∈ Ioo (0 : ℝ) 1) (K : ℝ → ℝ → ℝ)
    (hK : IsAllocationKernel K) :
    ((∀ (n : ℕ) (F : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (F i)], IsAtomlessInput F →
        ∀ i, inputLoad Γ K F i ≤ 1) ↔ (⨆ lam : Profile, loadK Γ K lam.1) ≤ 1) ∧
      ((⨆ lam : Profile, loadK Γ K lam.1) ≤ 1 →
        ∀ (n : ℕ) (F : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (F i)], IsAtomlessInput F →
          ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (V : Fin n → Ω → ℝ)
            (T : Fin n → Ω → WithTop ℝ), IsKernelRun Γ K F P V T →
            ItemwiseGuarantee Γ F P V (fun ω => kernelIndex K F (fun j => T j ω) (fun j => V j ω))) ∧
      ((⨆ lam : Profile, loadK Γ K lam.1) ≤ 1 →
        ∀ (n : ℕ) (F : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (F i)], IsInput F →
          ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (V Z : Fin n → Ω → ℝ)
            (T : Fin n → Ω → WithTop ℝ), IsScoreRun Γ K F P V Z T →
            ENNReal.ofReal Γ * ∫⁻ ω, (⨆ i, ENNReal.ofReal (V i ω)) ∂P ≤
              ∫⁻ ω, ENNReal.ofReal (algValue (scoreIndex K F (fun j => T j ω) (fun j => V j ω)
                (fun j => Z j ω)) (fun j => V j ω)) ∂P) := by sorry

end OrderSelProphet.Kernel
