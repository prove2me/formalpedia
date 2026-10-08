-- Prove2me | Theorems.Thm_FriendlyShadow_Gaussian_lemma_25
-- name    : FriendlyShadow.Gaussian.lemma_25
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T20:17:37.462592+00:00
-- url     : https://prove2.me/theorems/d4b9fed3-b60a-4360-93dd-e704a7d6a4e8
-- title:
--   Lemma 25, p. 22 — E|edges(Q ∩ W)| ≤ 2 + E[perimeter(Q ∩ W)] / min_{I∈B} E[length(conv(aᵢ : i ∈ I) ∩ W) | E_I]
-- statement:
--   Let $n\ge d\ge3$, let $W\subseteq\mathbb R^d$ be a fixed plane, and let $a_1,\dots,a_n$ be independent with probability densities $\mu_1,\dots,\mu_n$. Write $Q=\operatorname{conv}(a_1,\dots,a_n)$, $E_I$ for the event that $\operatorname{conv}(a_i:i\in I)\cap W$ is an edge of $Q\cap W$, and
--   $$B=\Big\{I\subseteq[n]:\ |I|=d,\ \Pr[E_I]\ge 2\tbinom nd^{-1}\Big\}.$$
--   The paper's statement is
--   $$\mathbb E\big[|\operatorname{edges}(Q\cap W)|\big]\le 2+\frac{\mathbb E[\operatorname{perimeter}(Q\cap W)]}{\min_{I\in B}\mathbb E[\operatorname{length}(\operatorname{conv}(a_i:i\in I)\cap W)\mid E_I]} .$$
--   In multiplied-out form: if $m\in[0,\infty]$ satisfies $m\Pr[E_I]\le\mathbb E[\operatorname{length}(\operatorname{conv}(a_i:i\in I)\cap W)\,;\,E_I]$ for every $I\in B$, then the edge count is a.e. measurable and
--   $$m\,\mathbb E\big[|\operatorname{edges}(Q\cap W)|\big]\le 2m+\mathbb E[\operatorname{perimeter}(Q\cap W)] .$$
--
--   This reduces the shadow bound to an upper bound on the expected perimeter (Lemma 26) and a lower bound on the conditional edge lengths (Lemmas 29–41).
--
--   **Formalization Note** The conditional expectation is a ratio, so the lemma is stated for every lower bound $m$ of the minimum; taking $m$ equal to the minimum gives the page's inequality, and $B=\emptyset$ is covered. Expectations are lower Lebesgue integrals in $[0,\infty]$; the conclusion also asserts a.e. measurability of the edge count, so that its integral is a genuine expectation. Of the standing assumptions of §3.1.2 only the densities (which give the paper's non-degeneracy conditions almost surely), $n\ge d\ge3$ and $\dim W=2$ are kept, because the proof uses nothing else.
-- source:
--   Dadush & Huiberts, arXiv:1711.05667v4, Lemma 25 with Defs 23–24, p. 22 (proof p. 23)

import Mathlib
import Definitions.Def_FriendlyShadow_Gaussian_Model

open MeasureTheory
open scoped RealInnerProductSpace ENNReal

namespace FriendlyShadow.Gaussian

/-- Lemma 25 (p. 22), cross-multiplied. Rows `a₁, …, aₙ` independent with densities `μ i`,
`n ≥ d ≥ 3`, `W` a fixed plane. If `m` is a lower bound for
`E[length(conv(aᵢ : i ∈ I) ∩ W) | E_I]` for every `I` in
`B = {I : |I| = d, Pr[E_I] ≥ 2·C(n,d)⁻¹}` (written `m · Pr[E_I] ≤ E[length; E_I]`), then
`m · E|edges(Q ∩ W)| ≤ 2m + E[perimeter(Q ∩ W)]`. -/
theorem lemma_25 {d n : ℕ} (hd : 3 ≤ d) (hdn : d ≤ n)
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin d))) (hW : Module.finrank ℝ W = 2)
    (μ : Fin n → EuclideanSpace ℝ (Fin d) → ℝ) (hμ : ∀ i, IsDensity (μ i)) (m : ℝ≥0∞)
    (hm : ∀ I : Finset (Fin n), I.card = d →
      ENNReal.ofReal (2 / (n.choose d : ℝ)) ≤ rowLaw μ {a | edgeEvent W a I} →
      m * rowLaw μ {a | edgeEvent W a I} ≤
        ∫⁻ a in {a | edgeEvent W a I}, edgeLen W a I ∂(rowLaw μ)) :
    AEMeasurable (fun a => (edgeCount (polygon W a) : ℝ≥0∞)) (rowLaw μ) ∧
    m * ∫⁻ a, (edgeCount (polygon W a) : ℝ≥0∞) ∂(rowLaw μ) ≤
      2 * m + ∫⁻ a, perimeter (polygon W a) ∂(rowLaw μ) := by sorry

end FriendlyShadow.Gaussian
