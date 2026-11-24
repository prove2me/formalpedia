-- Prove2me | Theorems.Thm_HLambdaG_Main_Supplement_theorem_1_e_corrected
-- name    : HLambdaG.Main.Supplement.theorem_1_e_corrected
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T01:01:28.265809+00:00
-- url     : https://prove2.me/theorems/64e8a2a3-31eb-479b-9d46-e4bb774d6f46
-- title:
--   Theorem 1(e), p. 639 (corrected: under the conditions of (a)) — if H or G converges, lim sup H ≤ lim inf λG
-- statement:
--   Let $F(s,t)$ be a cumulative input with marginal averages $G(s)=s^{-1}F(s,\infty)$ and $H(t)=t^{-1}F(\infty,t)$. Let $T_1$ be a time change with left limits $T_1(s-)$. Suppose $0<\lambda<\infty$, that
--   $$
--   s^{-1}T_1(s)\to\lambda^{-1}\quad\text{and}\quad s^{-1}\bigl[F(s,T_1(s-))-F(\infty,T_1(s-))\bigr]\to0\qquad(s\to\infty), \tag{14}
--   $$
--   and that either $H(t)\to H$ for some finite $H$ or $G(s)\to G$ for some finite $G$. Then
--   $$
--   \limsup_{t\to\infty}H(t)\;\le\;\liminf_{s\to\infty}\lambda G(s).
--   $$
--
--   Under (14), the time average $H$ is asymptotically at most $\lambda G$. Once either average converges, this becomes a single inequality. Part (d) is the mirror statement under (15).
--
--   **Formalization Note** The printed part (e) reads "Under the conditions of (b)". As with parts (a) and (b), whose corrected forms are the published base items, the hypotheses are interchanged in print. The upper bound on $H$ comes from (14), so the conditions here are those of the corrected (a): $T_1$ and (14), with $T_1(s-)$ the published left limit, where $T_1(0-)=0$. The printed reading is false. Take $T_k=k$ ($\lambda=1$) and $F_k(t)=1\{t\ge k/2\}$ in the §1.1 setting. Condition (15) holds with $T_2=T_1$, and $G(n)=1$ but $H(t)\to2$, so $\limsup H=2>1=\liminf\lambda G$. The lim inf and lim sup are taken in the extended reals.
--
--   Differences from the source:
--
--   - correction: Under the conditions of (b) (s⁻¹T₂(s) → λ⁻¹ and (15)) → the conditions of (a): s⁻¹T₁(s) → λ⁻¹ and (14) (Cond14 C τ₁); reason: the printed (a)/(b) hypotheses are interchanged (base items theorem_1_a_corrected / theorem_1_b_corrected); counterexample to the printed form: §1.1 with T_k = k, F_k(t) = 1{t ≥ k/2} satisfies (15) with T₂ = T₁, G ≡ 1, H → 2
--   - encoding: lim inf / lim sup, possibly infinite → Filter.liminf / Filter.limsup of the EReal coercion (published liminfE / limsupE), with λ multiplied inside the real function; reason: Lean convention; a real lim inf/lim sup of an unbounded function would be a junk value, and EReal keeps the page's possibly infinite values
-- source:
--   Glynn and Whitt, Extensions of the queueing relations L = λW and H = λG, Oper. Res. 37 (1989), p. 639, Theorem 1(e) (hypotheses of Theorem 1(a), as corrected in the published HLambdaG.Main.theorem_1_a_corrected); https://doi.org/10.1287/opre.37.4.634

import Mathlib
import Definitions.Def_HLambdaG_Main_Setting

open scoped NNReal

namespace HLambdaG.Main.Supplement

open Filter Topology

/-- Theorem 1(e), p. 639, corrected: under the conditions of the (corrected) part (a),
i.e. `s⁻¹T₁(s) → λ⁻¹` and (14), if `H(t)` or `G(s)` has a finite limit then
`lim sup H(t) ≤ lim inf λG(s)`. -/
theorem theorem_1_e_corrected
    (C : CumulativeInput) (τ₁ : TimeChange) (lam : ℝ) (hlam : 0 < lam)
    (hT₁ : Tendsto (fun s : ℝ≥0 => (τ₁.T s : ℝ) / (s : ℝ)) atTop (𝓝 lam⁻¹))
    (h14 : Cond14 C τ₁)
    (hlim : (∃ h : ℝ, Tendsto (H C) atTop (𝓝 h)) ∨ (∃ g : ℝ, Tendsto (G C) atTop (𝓝 g))) :
    limsupE (H C) ≤ liminfE (fun s => lam * G C s) := by sorry

end HLambdaG.Main.Supplement
