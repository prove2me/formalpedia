-- Prove2me | Theorems.Thm_OrderSelProphet_Kernel_theorem_6_1
-- name    : OrderSelProphet.Kernel.theorem_6_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:59:16.70962+00:00
-- url     : https://prove2.me/theorems/aaeb96be-00a5-4f99-aa71-0976d51853a9
-- title:
--   Theorem 6.1 — $K_1$ is an allocation kernel, $\sup_\lambda\ell_{\Gamma_1}(K_1,\lambda)<1$, construction feasible with (1), $\mathbb E[\mathrm{ALG}]\ge\Gamma_1\mathbb E[\mathrm{OPT}]$
-- statement:
--   Let $\Gamma_1=74500001/10^8$ and let $K_1$ be the kernel (68) built from Table 5. Then:
--
--   1. $K_1$ is an allocation kernel;
--   2. $\sup_{\lambda\in\Lambda}\ell_{\Gamma_1}(K_1,\lambda)<1$ (70);
--   3. consequently (Proposition 4.1) the prescribed arrival construction is universally feasible at $\Gamma_1$: on every atomless input of independent nonnegative values its allocations satisfy (4), every item's load is at most one, and it satisfies the exact item-wise guarantee (1);
--   4. moreover it yields an order-selection algorithm for arbitrary independent nonnegative values (atoms allowed) — the construction run on the tie-broken scores of Appendix H — with
--   $$\mathbb E[\mathrm{ALG}]\ge\Gamma_1\,\mathbb E[\mathrm{OPT}].$$
--
--   Differences from the source:
--   - generalization: inputs with n ≥ 2 items (§2, p. 6: 'The case n = 1 is immediate, so we assume n ≥ 2') → every input with n ≥ 1 items (IsInput requires 0 < n); reason: every n ≥ 2 input is included, so the statement specializes to the source's; the n = 1 case is the 'immediate' one
--   - encoding: sup_{λ∈Λ} ℓ_{Γ1}(K1, λ) < 1 → (⨆ λ : Profile, loadK Γ1 K1 λ) < 1 in ℝ≥0∞; reason: the supremum of [0,∞]-valued loads; equivalent to ∃ c < 1 bounding every load
--   - encoding: Λ: measurable λ : [0,1] → [0,1], identified when equal a.e. → Profile: measurable functions ℝ → ℝ with values in [0,1] on [0,1]; quantifying over representatives; reason: every quantity depends only on the a.e. class on [0,1]; a measurable function on [0,1] extends measurably to ℝ
--   - encoding: B_i(t) = B_{K,λ_i}(t) = ∫_0^1 λ_i(u) K(t,u) du with λ_i the profile (10) of item i → inputAlloc K F i t = E[1{I* = i} K(t, U)] with U = 1 − F_max(V_i) on {I* = i}; reason: equal by (10); this avoids choosing a version of λ_i
--   - reading: 'the prescribed arrival construction is universally feasible' → its allocations satisfy (4) (IsAllocation) and every item's load is ≤ 1; reason: feasibility of the construction (p. 8) presupposes (4), which Theorem 3.4 provides for kernels
--   - encoding: the item-wise guarantee (1): P(I = i | V_i = v) = Γ ∏_{j≠i} F_j(v) for F_i-a.e. v → ItemwiseGuarantee: P(I = i, V_i ∈ E) = Γ ∫_E ∏_{j≠i} F_j dF_i for every Borel E; reason: the integrated form is the definition of the conditional probability; it holds for all Borel E iff the a.e. identity holds
--   - encoding: the arrival-time algorithm of §2.1: T_i ~ G_i on [0,1] ∪ {†} independent of each other and of the values; inspect in arrival order with a fixed tie rule; accept the first item with U_i ≤ y_i(T_i); I = † and ALG = 0 if none → a probability space with V_i, T_i measurable, P.map V_i = F_i, P.map T_i = G_i, the 2n σ-algebras mutually independent (iIndep); † = ⊤ in WithTop ℝ; I = runIndex (first passing item in the order (T_i, i)), none for †; ALG = algValue; reason: the fixed tie rule is 'smaller index first'; each item's test reads only its own (T_i, V_i) and the known laws
--   - encoding: Appendix H: the construction with kernel K run on the scores X_i = F_mix(V_i^-) + Z_i(F_mix(V_i) − F_mix(V_i^-)), Z_i i.i.d. U[0,1] independent of the values → IsScoreRun: V_i ~ F_i, Z_i ~ U[0,1], T_i ~ the arrival laws of the kernel construction on the score laws (scoreLaw), the 3n σ-algebras mutually independent; I = scoreIndex (tests on the realized scores), ALG = V_I; reason: exactly the construction of Appendix H; item i's test reads only (T_i, V_i, Z_i)
--   - generalization: E[ALG] ≥ Γ E[OPT] (with E[ALG] = Γ E[OPT] 'whenever E[OPT] < ∞', p. 75) → Γ ∫⁻ max_i V_i dP ≤ ∫⁻ ALG dP in ℝ≥0∞; reason: covers E[OPT] = ∞ as well; for E[OPT] < ∞ it is the source's inequality
-- source:
--   Peng and Tang, Order-selection Prophet Inequality (Almost) Goes I.I.D., arXiv:2610.34892 (held file SHA-256 2f111b85…22dd), Theorem 6.1, p. 30 (proof in Appendix F, pp. 47–57; extension to atoms in Appendix H, p. 75)

import Mathlib
import Definitions.Def_OrderSelProphet_Kernel_K1
import Definitions.Def_OrderSelProphet_Kernel_Scores

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace OrderSelProphet.Kernel

/-- Theorem 6.1 (Universal guarantee for K1), p. 30: (i) `K1` is an allocation kernel;
(ii) `sup_λ ℓ_{Γ1}(K1, λ) < 1`; (iii) on every atomless input the K1 arrival construction at
`Γ1` is feasible and satisfies the exact item-wise guarantee (1); (iv) on arbitrary independent
nonnegative values, the construction run on the scores of Appendix H gives
`E[ALG] ≥ Γ1 E[OPT]`. -/
theorem theorem_6_1 :
    IsAllocationKernel K1 ∧
      (⨆ lam : Profile, loadK Gamma1 K1 lam.1) < 1 ∧
      (∀ (n : ℕ) (F : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (F i)], IsAtomlessInput F →
        IsAllocation F (inputAlloc K1 F) ∧ (∀ i, inputLoad Gamma1 K1 F i ≤ 1) ∧
          ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (V : Fin n → Ω → ℝ)
            (T : Fin n → Ω → WithTop ℝ), IsKernelRun Gamma1 K1 F P V T →
            ItemwiseGuarantee Gamma1 F P V
              (fun ω => kernelIndex K1 F (fun j => T j ω) (fun j => V j ω))) ∧
      ∀ (n : ℕ) (F : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (F i)], IsInput F →
        ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (V Z : Fin n → Ω → ℝ)
          (T : Fin n → Ω → WithTop ℝ), IsScoreRun Gamma1 K1 F P V Z T →
          ENNReal.ofReal Gamma1 * ∫⁻ ω, (⨆ i, ENNReal.ofReal (V i ω)) ∂P ≤
            ∫⁻ ω, ENNReal.ofReal (algValue (scoreIndex K1 F (fun j => T j ω) (fun j => V j ω)
              (fun j => Z j ω)) (fun j => V j ω)) ∂P := by sorry

end OrderSelProphet.Kernel
