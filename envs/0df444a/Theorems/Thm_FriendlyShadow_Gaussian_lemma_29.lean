-- Prove2me | Theorems.Thm_FriendlyShadow_Gaussian_lemma_29
-- name    : FriendlyShadow.Gaussian.lemma_29
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T20:18:13.317704+00:00
-- url     : https://prove2.me/theorems/c42de5e9-cc96-456f-a785-ce35c13fda54
-- title:
--   Lemma 29, p. 24 — E[length(conv(a₁,…,a_d) ∩ W) | E] ≥ E[length(conv(a₁,…,a_d) ∩ W) | D, E]/2
-- statement:
--   Let $n\ge d\ge3$, let $W$ be a fixed plane, and let $a_1,\dots,a_n$ be independent with probability densities whose means satisfy $\|\bar a_i\|\le1$ and whose cutoff radii $R_{n,d}=R(1/(d\binom nd))$ are at most $R$. Let $I\subseteq[n]$ with $|I|=d$ and $\Pr[E_I]\ge 2\binom nd^{-1}$, i.e. $I\in B$. Let $D$ be the bounded diameter event: $\|\pi_{\omega^\perp}(a_i)-\pi_{\omega^\perp}(a_j)\|\le 2+2R$ for all $i,j\in I$, where $\omega$ spans the direction of $\operatorname{aff}(a_i:i\in I)\cap W$. Then
--   $$\mathbb E\big[\operatorname{length}(\operatorname{conv}(a_i:i\in I)\cap W)\mid E_I\big]\ \ge\ \tfrac12\,\mathbb E\big[\operatorname{length}(\operatorname{conv}(a_i:i\in I)\cap W)\mid D, E_I\big],$$
--   stated multiplied out as
--   $$\mathbb E[\operatorname{length};E_I\cap D]\cdot\Pr[E_I]\ \le\ 2\,\mathbb E[\operatorname{length};E_I]\cdot\Pr[E_I\cap D].$$
--
--   Conditioning on $D$ costs at most a factor $2$, which lets the later lemmas assume the simplex has bounded diameter in the directions orthogonal to the edge.
--
--   **Formalization Note** The paper writes $I=[d]$ "without loss of generality"; here $I$ is general. The direction of $l=H\cap W$ is the intersection of the direction of $\operatorname{aff}(a_i:i\in I)$ with $W$. The multiplied-out form avoids division by $\Pr[E_I\cap D]$ (the proof shows it is positive). Expectations are lower Lebesgue integrals in $[0,\infty]$. Of the standing assumptions only the centers and cutoff radii (used in the proof) and $n\ge d\ge3$, $\dim W=2$ are kept.
-- source:
--   Dadush & Huiberts, arXiv:1711.05667v4, Lemma 29 with Defs 27–28, p. 24

import Mathlib
import Definitions.Def_FriendlyShadow_Gaussian_Model

open MeasureTheory
open scoped RealInnerProductSpace ENNReal

namespace FriendlyShadow.Gaussian

/-- Lemma 29 (p. 24), cross-multiplied. Rows independent with densities `μ i`, centers of norm
at most `1`, cutoff radii `R(1/(d·C(n,d)))` at most `R`. For `I` with `|I| = d` and
`Pr[E_I] ≥ 2·C(n,d)⁻¹` (i.e. `I ∈ B`), with `D` the bounded diameter event of Definition 28,
`E[length | E_I] ≥ E[length | D, E_I]/2`, written as
`E[length; E_I ∩ D] · Pr[E_I] ≤ 2 · E[length; E_I] · Pr[E_I ∩ D]`. -/
theorem lemma_29 {d n : ℕ} (hd : 3 ≤ d) (hdn : d ≤ n)
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin d))) (hW : Module.finrank ℝ W = 2)
    (μ : Fin n → EuclideanSpace ℝ (Fin d) → ℝ) (hμ : ∀ i, IsDensity (μ i))
    (abar : Fin n → EuclideanSpace ℝ (Fin d)) (hmean : ∀ i, HasMean (μ i) (abar i))
    (habar : ∀ i, ‖abar i‖ ≤ 1) (R : ℝ)
    (hR : ∀ i, CutoffRadiusLE (μ i) (abar i) (cutoffLevel n d) R)
    (I : Finset (Fin n)) (hI : I.card = d)
    (hB : ENNReal.ofReal (2 / (n.choose d : ℝ)) ≤ rowLaw μ {a | edgeEvent W a I}) :
    (∫⁻ a in {a | edgeEvent W a I ∧ boundedDiamEvent W a I R}, edgeLen W a I ∂(rowLaw μ)) *
        rowLaw μ {a | edgeEvent W a I} ≤
      2 * (∫⁻ a in {a | edgeEvent W a I}, edgeLen W a I ∂(rowLaw μ)) *
        rowLaw μ {a | edgeEvent W a I ∧ boundedDiamEvent W a I R} := by sorry

end FriendlyShadow.Gaussian
