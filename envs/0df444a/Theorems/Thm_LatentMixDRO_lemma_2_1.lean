-- Prove2me | Theorems.Thm_LatentMixDRO_lemma_2_1
-- name    : LatentMixDRO.lemma_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:24:48.842987+00:00
-- url     : https://prove2.me/theorems/773ce18c-ebb6-4965-805f-3c9c8a6f539d
-- title:
--   Lemma 2.1 — the worst-case subpopulation risk is the CVaR dual
-- statement:
--   Let $P_X$ be a probability law on $\mathbb R^d$, $\alpha_0\in(0,\tfrac12)$, and $z$ an integrable function under $P_X$, standing for the conditional risk $x\mapsto\mathbb E[\ell(\theta;(x,Y))\mid X=x]$. Then
--
--   $$
--   \sup_{Q_0\in\mathcal P_{\alpha_0,X}}\mathbb E_{X\sim Q_0}[z(X)]=\inf_{\eta\in\mathbb R}\Big\{\frac1{\alpha_0}\mathbb E_{X\sim P_X}\big[(z(X)-\eta)_+\big]+\eta\Big\}.
--   $$
--
--   If in addition $0\le z\le M$ almost surely, then a minimizing $\eta$ exists, every minimizing $\eta$ lies in $[0,M]$, and the infimum over $\eta\in[0,M]$ has the same value.
--
--   This turns the worst case over subpopulations into a one-dimensional convex problem in $\eta$, which is the starting point of every later bound.
--
--   Differences from the source:
--   - reading: the infimizing $\eta$ lies in $[0,M]$ → a minimizer exists, every minimizer lies in $[0,M]$, and the infimum over $[0,M]$ equals the common value (display (35)); reason: the strongest reading of the sentence, and the one (35) proves
--   - encoding: $\mathbb E[\ell(\theta;(X,Y))\mid X]$ with $\mathbb E|\cdot|<\infty$ → an arbitrary $P_X$-integrable $z$; reason: every such $z$ is the conditional risk of $z(X)$, so no instance changes
--   - encoding: $\sup=\inf$ → `IsLUB` and `IsGLB` of one common value $v$; reason: Lean convention
-- source:
--   Duchi, Hashimoto & Namkoong, Distributionally Robust Losses for Latent Covariate Mixtures, arXiv:2007.13982v2, Lemma 2.1, p.6, display (7), and display (35), p.33

import Mathlib
import Definitions.Def_LatentMixDRO_uncertaintySet
import Definitions.Def_LatentMixDRO_cvarObj

open MeasureTheory

namespace LatentMixDRO

/-- Lemma 2.1: the worst-case subpopulation risk is the CVaR dual. If `z` is `P_X`-integrable, then
`sup_{Q₀ ∈ P_{α₀,X}} E_{X∼Q₀}[z(X)] = inf_{η ∈ ℝ} {(1/α₀) E_{X∼P_X}[(z(X) - η)₊] + η}` (7).
If moreover `0 ≤ z ≤ M` almost surely, the infimizing `η` lies in `[0, M]`.

Duchi, Hashimoto & Namkoong, arXiv:2007.13982v2, Lemma 2.1, p.6, display (7); the second claim with
display (35), p.33.

**Formalization Note.** `z` stands for `x ↦ E[ℓ(θ; (x, Y)) | X = x]`, and any integrable `z` is such a
function. The value is `v`, with `IsLUB`/`IsGLB`. "The infimizing `η` lies in `[0, M]`" is posed in
the strong reading: a minimizer exists, every minimizer lies in `[0, M]`, and the infimum over
`[0, M]` is still `v` (display (35)). -/
theorem lemma_2_1 {d : ℕ} (PX : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure PX]
    (z : EuclideanSpace ℝ (Fin d) → ℝ) (hz : Integrable z PX) (α₀ : ℝ) (hα₀ : 0 < α₀)
    (hα₀' : α₀ < 1 / 2) :
    ∃ v : ℝ,
      IsLUB {s | ∃ Q₀ ∈ uncertaintySet α₀ PX, s = ∫ x, z x ∂Q₀} v ∧
      IsGLB (Set.range (cvarObj α₀ PX z)) v ∧
      ∀ M : ℝ, (∀ᵐ x ∂PX, 0 ≤ z x ∧ z x ≤ M) →
        (∃ η₀, ∀ η, cvarObj α₀ PX z η₀ ≤ cvarObj α₀ PX z η) ∧
        (∀ η₀, (∀ η, cvarObj α₀ PX z η₀ ≤ cvarObj α₀ PX z η) → η₀ ∈ Set.Icc 0 M) ∧
        IsGLB (cvarObj α₀ PX z '' Set.Icc 0 M) v := by sorry

end LatentMixDRO
