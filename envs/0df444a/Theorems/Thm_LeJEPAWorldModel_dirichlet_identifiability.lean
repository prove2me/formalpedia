-- Prove2me | Theorems.Thm_LeJEPAWorldModel_dirichlet_identifiability
-- name    : LeJEPAWorldModel.dirichlet_identifiability
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T17:24:46.264014+00:00
-- url     : https://prove2.me/theorems/cdfefc9f-30a1-4542-a32f-419430748c11
-- title:
--   Theorem 5: identifiability via Dirichlet energy
-- statement:
--   Let $z,\eta\sim\mathcal N(0,I_N)$ be independent, and for $h:\mathbb R^N\to\mathbb R^N$ let
--
--   $$\mathcal L(h)=\lim_{\varepsilon\to0^+}\frac1\varepsilon\,\mathbb E\big[\|h(z+\sqrt\varepsilon\,\eta)-h(z)\|^2\big].$$
--
--   Let $h$ be a $C^1$ diffeomorphism of $\mathbb R^N$ that preserves the standard Gaussian measure. Suppose $h$ minimizes $\mathcal L$: the limit $\mathcal L(h)\in[0,\infty]$ exists and is at most $\mathcal L(h')$ for every Gaussian-preserving $C^1$ diffeomorphism $h'$ whose limit exists. Then $h(z)=Qz$ for all $z$, for some orthogonal $Q\in O(N)$.
--
--   This is a second, geometric proof of identifiability, in the small-noise regime: the Jacobian of a minimizer must be an isometry at every point.
--
--   **Formalization Note** The expectation is taken in $[0,\infty]$ so that it is defined for every $h$. The minimization ranges over the Gaussian-preserving $C^1$ diffeomorphisms for which the limit defining $\mathcal L$ exists.
-- source:
--   Klindt, LeCun and Balestriero, When Does LeJEPA Learn a World Model?, arXiv:2605.26379v2 (2026), Appendix E, Theorem 5, p. 28; setup in Appendix E.1, p. 28; proof in Appendix E.2, pp. 28-29

import Mathlib
import Definitions.Def_LeJEPAWorldModel_Basic

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace LeJEPAWorldModel

theorem dirichlet_identifiability (N : ℕ) (h : (Fin N → ℝ) → Fin N → ℝ)
    (hdiffeo : IsC1Diffeo h) (hpres : (stdGaussian N).map h = stdGaussian N) (L : ℝ≥0∞)
    (hL : Tendsto (dirichletQuotient N h) (𝓝[>] 0) (𝓝 L))
    (hmin : ∀ h' : (Fin N → ℝ) → Fin N → ℝ, IsC1Diffeo h' →
      (stdGaussian N).map h' = stdGaussian N → ∀ L' : ℝ≥0∞,
        Tendsto (dirichletQuotient N h') (𝓝[>] 0) (𝓝 L') → L ≤ L') :
    ∃ Q ∈ Matrix.orthogonalGroup (Fin N) ℝ, ∀ z, h z = Q.mulVec z := by sorry

end LeJEPAWorldModel
