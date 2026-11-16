-- Prove2me | Theorems.Thm_MaxCutMatrix2027_Upper_Supplement_ising_chi_square
-- name    : MaxCutMatrix2027.Upper.Supplement.ising_chi_square
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:09:21.693175+00:00
-- url     : https://prove2.me/theorems/0dfe52c1-c82d-4c15-8481-454dda1785f1
-- title:
--   Lemma 6.3 — Ising form of the χ² divergence for a fixed query graph
-- statement:
--   Let $n\ge2$, $0<\varepsilon\le1/160$, $\rho=40\varepsilon$, and let $H$ be any fixed query graph on $[n]$ (possibly empty) with $q=|E(H)|$ edges. Let $D_{1,H}$ and $D_{0,H}$ be the laws of the answer vector $(Y_{uv})_{\{u,v\}\in E(H)}$ under the yes and no laws of Definition 5.1. For independent uniform signs $\Xi_1,\dots,\Xi_n$,
--   $$1+\chi^2(D_{1,H}\|D_{0,H})=\mathbb E_\Xi\Bigl[\prod_{\{u,v\}\in E(H)}(1+\rho^2\Xi_u\Xi_v)\Bigr].$$
--   Moreover, if $a=e\rho^2\sqrt q<1$ ($e$ Euler's number), then
--   $$\chi^2(D_{1,H}\|D_{0,H})\le\frac{a^2}{1-a}.$$
--
--   This identity expresses the distinguishing power of a fixed query set as a high-temperature Ising partition function, and the bound drives the non-adaptive lower bound.
--
--   Differences from the source:
--   - encoding: vertices (variables) labelled by [n] → Fin n = {0,…,n−1}; reason: relabeling is bijective
--   - encoding: signs and edge indicators in {−1,1} (Y = −1 an edge) → Booleans (true ↦ sign 1; answer true = edge); reason: bijective relabeling; every quantity is transported unchanged
--   - encoding: the distributions D0, D1 and D1^joint of Definition 5.1 → explicit finite mass functions noLaw, yesLaw = ∑_σ yesJoint with yesJoint(σ,G) = 2^{-n} ∏_{u<v} Pr(Y_uv | σ); reason: these are exactly the product laws of Definition 5.1 and Eq. (35)
--   - encoding: χ²(D‖D') = E_{D'}[L²] − 1 → ∑_y D(y)²/D'(y) − 1; reason: D_{0,H}(y) = 2^{-q} > 0 for every y, so the two expressions coincide
--   - encoding: E_Ξ over independent uniform signs → 2^{-n} ∑ over all ξ ∈ {−1,1}^n; reason: the uniform law on the cube
-- source:
--   Songhua He, STOC 2027 submission #351 (October 2026), Lemma 6.3, p.30 (PDF p.30); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/351.pdf; PDF SHA-256 b38cd84079663d9e2eb7375d7bf1572d5dc7c2157cfaf90e175fd371a9503631

import Definitions.Def_MaxCutMatrix2027_Upper_Supplement_QueryModel
set_option autoImplicit false
open scoped BigOperators Classical

namespace MaxCutMatrix2027.Upper.Supplement

/-- Lemma 6.3, p.30: exact χ²/Ising identity (36) and the `a²/(1−a)` bound, for every fixed
query graph `H` (including the empty one), under the laws of Definition 5.1 with `ρ = 40ε`. -/
theorem ising_chi_square (n : ℕ) (hn : 2 ≤ n) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 160)
    (H : SimpleGraph (Fin n)) :
    let ρ : ℝ := 40 * ε
    let q : ℝ := (Nat.card H.edgeSet : ℝ)
    let χ2 : ℝ := chiSq (answerLaw (fun G => yesLaw ρ G) H) (answerLaw (fun G => noLaw G) H)
    let a : ℝ := Real.exp 1 * ρ ^ 2 * Real.sqrt q
    1 + χ2 = (1 / 2 : ℝ) ^ n * ∑ ξ : Fin n → Bool, ∏ e ∈ H.edgeFinset, (1 + ρ ^ 2 * signProd ξ e) ∧
    (a < 1 → χ2 ≤ a ^ 2 / (1 - a)) := by sorry

end MaxCutMatrix2027.Upper.Supplement
