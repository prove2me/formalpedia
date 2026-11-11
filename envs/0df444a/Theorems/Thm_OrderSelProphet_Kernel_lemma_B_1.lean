-- Prove2me | Theorems.Thm_OrderSelProphet_Kernel_lemma_B_1
-- name    : OrderSelProphet.Kernel.lemma_B_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:57:25.064016+00:00
-- url     : https://prove2.me/theorems/1069ddb5-858b-4013-b041-a053efc04026
-- title:
--   Lemma B.1 — rank representation: $P(R_i>u)=e^{-h_\lambda(u)}$, $U_i=x_\lambda(R_i)$ a.s., hence $A_i=A_\lambda$
-- statement:
--   Fix an atomless input and an item $i$ with profile $\lambda=\lambda_i$, and let $R_i=1-F_{\max}(V_i)$ be the rank of its value. Then
--
--   (a) $P(R_i>u)=e^{-h_\lambda(u)}$ for every $u\in[0,1)$;
--
--   (b) $U_i=x_\lambda(R_i)$ almost surely (with $x_\lambda(1)=1$).
--
--   Consequently the area curve of item $i$ is $A_i=A_\lambda$ on $[0,1]$, with $A_\lambda$ given by (38); in particular $A_i$ depends on the input only through $\lambda_i$.
--
--   Differences from the source:
--   - generalization: inputs with n ≥ 2 items (§2, p. 6: 'The case n = 1 is immediate, so we assume n ≥ 2') → every input with n ≥ 1 items (IsInput requires 0 < n); reason: every n ≥ 2 input is included, so the statement specializes to the source's; the n = 1 case is the 'immediate' one
--   - encoding: Λ: measurable λ : [0,1] → [0,1], identified when equal a.e. → Profile: measurable functions ℝ → ℝ with values in [0,1] on [0,1]; quantifying over representatives; reason: every quantity depends only on the a.e. class on [0,1]; a measurable function on [0,1] extends measurably to ℝ
--   - encoding: 'item i with profile λ = λ_i' → any profile λ with IsProfileOf F i λ (P(I* = i, U ≤ u) = ∫_0^u λ for u ∈ [0,1]); reason: this is definition (10); the conclusion depends only on the a.e. class of λ
--   - encoding: P(R_i > u), U_i = x_λ(R_i) a.s., A_i = A_λ → F_i{v : 1 − F_max(v) > u}; F_i-a.e. v, lossScore v = x_λ(1 − F_max v); EqOn on [0,1]; reason: R_i and U_i are functions of V_i ~ F_i; area curves are functions on [0,1]
-- source:
--   Peng and Tang, Order-selection Prophet Inequality (Almost) Goes I.I.D., arXiv:2610.34892 (held file SHA-256 2f111b85…22dd), Lemma B.1, p. 39

import Mathlib
import Definitions.Def_OrderSelProphet_Kernel_Profiles

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace OrderSelProphet.Kernel

/-- Lemma B.1 (Rank representation), p. 39: with `R_i = 1 - F_max(V_i)`,
(a) `P(R_i > u) = e^{-h_λ(u)}` for `u ∈ [0,1)`; (b) `U_i = x_λ(R_i)` almost surely; hence
`A_i = A_λ` on `[0,1]`. -/
theorem lemma_B_1 {n : ℕ} (F : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (F i)]
    (hF : IsAtomlessInput F) (i : Fin n) (lam : Profile) (hlam : IsProfileOf F i lam.1) :
    (∀ u ∈ Ico (0 : ℝ) 1, (F i {v | u < 1 - Fmax F v}).toReal = Real.exp (-hP lam.1 u)) ∧
      (∀ᵐ v ∂(F i), lossScore F i v = xP lam.1 (1 - Fmax F v)) ∧
      EqOn (inputArea F i) (areaP lam.1) (Icc 0 1) := by sorry

end OrderSelProphet.Kernel
