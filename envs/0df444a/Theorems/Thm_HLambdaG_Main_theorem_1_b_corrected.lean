-- Prove2me | Theorems.Thm_HLambdaG_Main_theorem_1_b_corrected
-- name    : HLambdaG.Main.theorem_1_b_corrected
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T08:44:51.325162+00:00
-- url     : https://prove2.me/theorems/a9f260d5-f4c6-4cc2-8af6-918b3d7fd36d
-- title:
--   Theorem 1(b), p. 639 — corrected lower bounds under (15)
-- statement:
--   Let $F$ be a cumulative input with marginal averages $G$ and $H$. Let $T_2$ be a time change with $T_2(s)/s\to\lambda^{-1}$ for $\lambda>0$, and assume condition (15): $[F(s,\infty)-F(s,T_2(s))]/s\to0$. Then
--
--   $$
--   \liminf_{t\to\infty}H(t)\geq\liminf_{s\to\infty}\lambda G(s),
--   \qquad
--   \limsup_{t\to\infty}H(t)\geq\limsup_{s\to\infty}\lambda G(s).
--   $$
--
--   These are the lower asymptotic bounds furnished by (15), without needing condition (14).
--
--   **Formalization Note** Printed Theorem 1(b) gives upper bounds and is false: the lump-input example described in the mission notes satisfies (15) but has $\liminf H=2>1=\liminf G$ at $\lambda=1$. The hypotheses of printed (a) and (b) are interchanged here. The intermediate $G(S_i(t))$ terms are omitted because they require continuity in the customer coordinate that the paper does not assume. Lim inf and lim sup take values in the extended reals; multiplication by $\lambda$ occurs before the embedding.
-- source:
--   Glynn and Whitt, Extensions of the queueing relations L = λW and H = λG, Oper. Res. 37 (1989), p. 639, Theorem 1(a)–(b), corrected pairing; https://doi.org/10.1287/opre.37.4.634

import Mathlib
import Definitions.Def_HLambdaG_Main_Setting

open scoped NNReal

namespace HLambdaG.Main

open Filter Topology

/-- Theorem 1(b), p. 639, with its printed bound direction corrected. -/
theorem theorem_1_b_corrected
    (C : CumulativeInput) (τ₂ : TimeChange) (lam : ℝ) (hlam : 0 < lam)
    (hT₂ : Tendsto (fun s : ℝ≥0 => (τ₂.T s : ℝ) / (s : ℝ)) atTop (𝓝 lam⁻¹))
    (h15 : Cond15 C τ₂) :
    liminfE (fun s => lam * G C s) ≤ liminfE (H C) ∧
      limsupE (fun s => lam * G C s) ≤ limsupE (H C) := by sorry

end HLambdaG.Main
