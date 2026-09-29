-- Prove2me | Theorems.Thm_LesHouchesWidth_kappa4_eq_covariance
-- name    : LesHouchesWidth.kappa4_eq_covariance
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T22:08:27.57439+00:00
-- url     : https://prove2.me/theorems/e847efd6-b0e4-4828-9275-f5e55dec7bd7
-- title:
--   Section 4.8, exercise: $\kappa_4^{(\ell)}=\mathrm{Cov}\big((z^{(\ell)}_i)^2,(z^{(\ell)}_j)^2\big)$ for $i\neq j$
-- statement:
--   Let $C_b\ge0$, $C_W>0$, $\sigma$ measurable and polynomially bounded, all widths $\ge1$, and $1\le\ell\le L+1$. For the network with Gaussian initialization at a fixed input $x$ and any two distinct neurons $i\neq j$ of layer $\ell$,
--   $$\kappa^{(\ell)}_4=\mathrm{Cov}\Big(\big(z^{(\ell)}_i\big)^2,\ \big(z^{(\ell)}_j\big)^2\Big).$$
--
--   This identifies $\kappa_4$ as a measure of correlations between neurons.
-- source:
--   Bahri, Hanin, Brossollet, Erba, Keup, Pacelli, Simon, *Les Houches Lectures on Deep Learning at Large & Infinite Width*, arXiv:2309.01592v3 (https://arxiv.org/abs/2309.01592), pp. 32–33, Section 4.8, exercise following the definition of $\kappa_4$.

import Mathlib
import Definitions.Def_LesHouchesWidth_GaussianMLP
import Definitions.Def_LesHouchesWidth_FiniteWidth

namespace LesHouchesWidth

open MeasureTheory ProbabilityTheory

theorem kappa4_eq_covariance (Cb CW : ℝ) (hCb : 0 ≤ Cb) (hCW : 0 < CW)
    (σ : ℝ → ℝ) (hσ : Measurable σ) (hσ_poly : PolyBounded σ)
    (n : ℕ → ℕ) (L : ℕ) (hn : ∀ ℓ ≤ L + 1, 1 ≤ n ℓ) (x : Fin (n 0) → ℝ)
    (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (hℓL : ℓ ≤ L + 1) (i j : Fin (n ℓ)) (hij : i ≠ j) :
    kappa4 Cb CW σ n L x ℓ i =
      covariance (fun θ => (mlpZ Cb CW σ θ x ℓ i) ^ 2) (fun θ => (mlpZ Cb CW σ θ x ℓ j) ^ 2)
        (stdGaussianParams n L) := by sorry

end LesHouchesWidth
