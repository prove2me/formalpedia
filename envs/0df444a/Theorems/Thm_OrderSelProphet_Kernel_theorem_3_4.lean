-- Prove2me | Theorems.Thm_OrderSelProphet_Kernel_theorem_3_4
-- name    : OrderSelProphet.Kernel.theorem_3_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:57:11.992951+00:00
-- url     : https://prove2.me/theorems/fb6a6f78-5a9d-4992-b2c5-877e6d254473
-- title:
--   Theorem 3.4 — characterization of local constructions: exactly the functionals $\mathfrak B[A_\lambda]=B_{K,\lambda}$ of an allocation kernel $K$, unique up to a null set of ranks
-- statement:
--   A functional $\mathfrak B$ is a local construction (Definition 3.1) if and only if there exists an allocation kernel $K$ (Definition 3.3) such that
--   $$\mathfrak B[A_\lambda](t)=B_{K,\lambda}(t)=\int_0^1\lambda(u)K(t,u)\,du\qquad(\lambda\in\Lambda,\ t\in[0,1]).\quad(17)$$
--   The kernel is unique up to a null set of maximum ranks, simultaneously for all $t$: if $K$ and $K'$ both satisfy (17), there is a Lebesgue-null set $N$ with $K(t,u)=K'(t,u)$ for all $u\in[0,1]\setminus N$ and all $t\in[0,1]$.
--
--   Differences from the source:
--   - encoding: Λ: measurable λ : [0,1] → [0,1], identified when equal a.e. → Profile: measurable functions ℝ → ℝ with values in [0,1] on [0,1]; quantifying over representatives; reason: every quantity depends only on the a.e. class on [0,1]; a measurable function on [0,1] extends measurably to ℝ
--   - encoding: a functional B on 𝒜 → 𝔅 : (Icc 0 1 → ℝ) → ℝ → ℝ, constrained only on AreaClass (Definition 3.1) and on the curves A_λ (17); reason: area curves are functions on [0,1]; values of 𝔅 off 𝒜 play no role
--   - encoding: Definition 3.1's inputs (n ≥ 2) → IsLocalConstruction quantifies over atomless inputs with n ≥ 1; reason: for n = 1, (8) follows from the two-item input with profiles (1, 0), so the class of local constructions is the same
--   - encoding: jointly measurable K : [0,1]² → [0,1] → K : ℝ → ℝ → ℝ, measurable as a function on the subtype [0,1] × [0,1], with values in [0,1] there; reason: values outside [0,1]² are never used
-- source:
--   Peng and Tang, Order-selection Prophet Inequality (Almost) Goes I.I.D., arXiv:2610.34892 (held file SHA-256 2f111b85…22dd), Theorem 3.4, p. 11 (necessity and uniqueness in Appendix C, pp. 42–43)

import Mathlib
import Definitions.Def_OrderSelProphet_Kernel_Profiles

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace OrderSelProphet.Kernel

/-- Theorem 3.4 (Characterization of local constructions), p. 11 (necessity and uniqueness in
Appendix C, pp. 42–43). -/
theorem theorem_3_4 (𝔅 : (Icc (0 : ℝ) 1 → ℝ) → ℝ → ℝ) :
    (IsLocalConstruction 𝔅 ↔ ∃ K : ℝ → ℝ → ℝ, IsAllocationKernel K ∧ Represents K 𝔅) ∧
      ∀ K K' : ℝ → ℝ → ℝ, IsAllocationKernel K → Represents K 𝔅 →
        IsAllocationKernel K' → Represents K' 𝔅 →
        ∃ N : Set ℝ, volume N = 0 ∧ ∀ u ∈ Icc (0 : ℝ) 1 \ N, ∀ t ∈ Icc (0 : ℝ) 1, K t u = K' t u := by sorry

end OrderSelProphet.Kernel
