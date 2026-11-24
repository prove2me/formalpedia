-- Prove2me | Theorems.Thm_HLambdaG_Main_Supplement_theorem_1_d_corrected
-- name    : HLambdaG.Main.Supplement.theorem_1_d_corrected
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T01:00:24.372833+00:00
-- url     : https://prove2.me/theorems/0a4e2cf5-faa8-4155-8d05-b2e40242b232
-- title:
--   Theorem 1(d), p. 639 (corrected: under the conditions of (b)) — if H or G converges, lim inf H ≥ lim sup λG
-- statement:
--   Let $F(s,t)$ be a cumulative input: real valued on $[0,\infty)^2$, nondecreasing in each variable, with finite limits $F(s,\infty)$ and $F(\infty,t)$. Let $G(s)=s^{-1}F(s,\infty)$ and $H(t)=t^{-1}F(\infty,t)$ be its marginal averages (1). Let $T_2$ be a time change (nonnegative, finite, nondecreasing, right-continuous, $T_2(s)\to\infty$). Suppose $0<\lambda<\infty$, that
--   $$
--   s^{-1}T_2(s)\to\lambda^{-1}\quad\text{and}\quad s^{-1}\bigl[F(s,\infty)-F(s,T_2(s))\bigr]\to0\qquad(s\to\infty), \tag{15}
--   $$
--   and that either $H(t)\to H$ for some finite $H$ or $G(s)\to G$ for some finite $G$. Then
--   $$
--   \liminf_{t\to\infty}H(t)\;\ge\;\limsup_{s\to\infty}\lambda G(s).
--   $$
--
--   Under (15), the time average $H$ is asymptotically at least $\lambda G$. Once either average converges, this becomes a single inequality between a lim inf and a lim sup. Part (e) is the mirror statement under (14). Together they give part (f).
--
--   **Formalization Note** The printed part (d) invokes (a), hence (14). Take $T_k=k$, $F_k(t)=1\{t\ge2k\}$ and $\lambda=1$. For each finite $t$ only finitely many terms are nonzero, all marginal limits are finite, and (14) vanishes identically. Yet $G(s)\to1$ and $H(t)\to1/2$, contradicting the printed $\liminf H\ge\limsup G$. The corrected part invokes (15), as the corrected one-sided bounds require. The finite-limit disjunction is retained, and lim inf and lim sup are extended real.
--
--   Differences from the source:
--
--   - correction: Under the conditions of (a) (s⁻¹T₁(s) → λ⁻¹ and (14)) → the conditions of (b): s⁻¹T₂(s) → λ⁻¹ and (15) (Cond15 C τ₂); reason: the printed (a)/(b) hypotheses are interchanged; with T_k=k and F_k(t)=1{t ≥ 2k}, (14) holds identically but G → 1 and H → 1/2, refuting printed (d)
--   - encoding: lim inf / lim sup, possibly infinite → Filter.liminf / Filter.limsup of the EReal coercion (published liminfE / limsupE), with λ multiplied inside the real function; reason: Lean convention; a real lim inf/lim sup of an unbounded function would be a junk value, and EReal keeps the page's possibly infinite values
-- source:
--   Glynn and Whitt, Extensions of the queueing relations L = λW and H = λG, Oper. Res. 37 (1989), p. 639, Theorem 1(d) (hypotheses of Theorem 1(b), as corrected in the published HLambdaG.Main.theorem_1_b_corrected); https://doi.org/10.1287/opre.37.4.634

import Mathlib
import Definitions.Def_HLambdaG_Main_Setting

open scoped NNReal

namespace HLambdaG.Main.Supplement

open Filter Topology

/-- Theorem 1(d), p. 639, corrected: under the conditions of the (corrected) part (b),
i.e. `s⁻¹T₂(s) → λ⁻¹` and (15), if `H(t)` or `G(s)` has a finite limit then
`lim inf H(t) ≥ lim sup λG(s)`. -/
theorem theorem_1_d_corrected
    (C : CumulativeInput) (τ₂ : TimeChange) (lam : ℝ) (hlam : 0 < lam)
    (hT₂ : Tendsto (fun s : ℝ≥0 => (τ₂.T s : ℝ) / (s : ℝ)) atTop (𝓝 lam⁻¹))
    (h15 : Cond15 C τ₂)
    (hlim : (∃ h : ℝ, Tendsto (H C) atTop (𝓝 h)) ∨ (∃ g : ℝ, Tendsto (G C) atTop (𝓝 g))) :
    limsupE (fun s => lam * G C s) ≤ liminfE (H C) := by sorry

end HLambdaG.Main.Supplement
