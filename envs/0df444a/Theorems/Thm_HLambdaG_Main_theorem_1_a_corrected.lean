-- Prove2me | Theorems.Thm_HLambdaG_Main_theorem_1_a_corrected
-- name    : HLambdaG.Main.theorem_1_a_corrected
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T08:44:39.191838+00:00
-- url     : https://prove2.me/theorems/8fa33e7c-8223-4d37-8400-368e57600541
-- title:
--   Theorem 1(a), p. 639 — corrected upper bounds under (14)
-- statement:
--   Let $F$ be a cumulative input with marginal averages $G$ and $H$. Let $T_1$ be a time change with $T_1(s)/s\to\lambda^{-1}$ for $\lambda>0$, and assume condition (14): $[F(s,T_1(s-))-F(\infty,T_1(s-))]/s\to0$. Then
--
--   $$
--   \liminf_{t\to\infty}H(t)\leq\liminf_{s\to\infty}\lambda G(s),
--   \qquad
--   \limsup_{t\to\infty}H(t)\leq\limsup_{s\to\infty}\lambda G(s).
--   $$
--
--   These are the upper asymptotic bounds furnished by (14), without needing condition (15).
--
--   **Formalization Note** Printed Theorem 1(a) gives lower bounds and is false: the power-of-two waiting-time example described in the mission notes satisfies (14), has $H\to1$, and has $\limsup G=2$. The hypotheses of printed (a) and (b) are interchanged here. The intermediate $G(S_i(t))$ terms are omitted because they require continuity in the customer coordinate that the paper does not assume. Lim inf and lim sup take values in the extended reals; multiplication by $\lambda$ occurs before the embedding.
-- source:
--   Glynn and Whitt, Extensions of the queueing relations L = λW and H = λG, Oper. Res. 37 (1989), p. 639, Theorem 1(a)–(b), corrected pairing; https://doi.org/10.1287/opre.37.4.634

import Mathlib
import Definitions.Def_HLambdaG_Main_Setting

open scoped NNReal

namespace HLambdaG.Main

open Filter Topology

/-- Theorem 1(a), p. 639, with its printed bound direction corrected. -/
theorem theorem_1_a_corrected
    (C : CumulativeInput) (τ₁ : TimeChange) (lam : ℝ) (hlam : 0 < lam)
    (hT₁ : Tendsto (fun s : ℝ≥0 => (τ₁.T s : ℝ) / (s : ℝ)) atTop (𝓝 lam⁻¹))
    (h14 : Cond14 C τ₁) :
    liminfE (H C) ≤ liminfE (fun s => lam * G C s) ∧
      limsupE (H C) ≤ limsupE (fun s => lam * G C s) := by sorry

end HLambdaG.Main
