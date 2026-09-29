-- Prove2me | Theorems.Thm_LesHouchesWidth_conditional_gaussian_next_layer
-- name    : LesHouchesWidth.conditional_gaussian_next_layer
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T22:02:56.420867+00:00
-- url     : https://prove2.me/theorems/49daa880-9373-443b-9d6a-849285e2653f
-- title:
--   Lemma 4.4: conditional Gaussianity of the next layer and $\kappa_4^{(\ell+1)}=\mathrm{Var}[\Sigma^{(\ell)}]$
-- statement:
--   Let $C_b\ge0$, $C_W>0$, $\sigma$ measurable and polynomially bounded, $n_0,\dots,n_{L+1}\ge1$, and $1\le\ell\le L$. For the network with Gaussian initialization (119) at a fixed input $x$:
--
--   1. conditional on $z^{(\ell)}$, the vector $(z^{(\ell+1)}_i)_{i\le n_{\ell+1}}$ is Gaussian with mean $0$ and covariance $\Sigma^{(\ell)}\cdot I$, where
--   $$\Sigma^{(\ell)}=C_b+\frac{C_W}{n_\ell}\sum_{j=1}^{n_\ell}\sigma\big(z^{(\ell)}_j\big)^2;$$
--   2. for every neuron $i$, $\kappa^{(\ell+1)}_4=\mathrm{Var}\big[\Sigma^{(\ell)}\big]$.
--
--   This reduces the four-point function to the fluctuations of a collective observable of the previous layer.
--
--   **Formalization Note** The conditional law is expressed with Mathlib's regular conditional distribution `condDistrib`, as an identity holding for almost every value of $z^{(\ell)}$. The characteristic-function identity in the lemma is equivalent to part 1.
-- source:
--   Bahri, Hanin, Brossollet, Erba, Keup, Pacelli, Simon, *Les Houches Lectures on Deep Learning at Large & Infinite Width*, arXiv:2309.01592v3 (https://arxiv.org/abs/2309.01592), pp. 34–35, Lemma 4.4 and its proof (Section 4.9.2).

import Mathlib
import Definitions.Def_LesHouchesWidth_GaussianMLP
import Definitions.Def_LesHouchesWidth_FiniteWidth

namespace LesHouchesWidth

open MeasureTheory ProbabilityTheory

theorem conditional_gaussian_next_layer (Cb CW : ℝ) (hCb : 0 ≤ Cb) (hCW : 0 < CW)
    (σ : ℝ → ℝ) (hσ : Measurable σ) (hσ_poly : PolyBounded σ)
    (n : ℕ → ℕ) (L : ℕ) (hn : ∀ ℓ ≤ L + 1, 1 ≤ n ℓ) (x : Fin (n 0) → ℝ)
    (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (hℓL : ℓ ≤ L) :
    (∀ᵐ y ∂((stdGaussianParams n L).map (fun θ => mlpZ Cb CW σ θ x ℓ)),
      condDistrib (fun θ => (WithLp.equiv 2 (Fin (n (ℓ + 1)) → ℝ)).symm (mlpZ Cb CW σ θ x (ℓ + 1)))
          (fun θ => mlpZ Cb CW σ θ x ℓ) (stdGaussianParams n L) y =
        multivariateGaussian 0 (collectiveSigma Cb CW σ n ℓ y • (1 : Matrix _ _ ℝ))) ∧
    (∀ i : Fin (n (ℓ + 1)),
      kappa4 Cb CW σ n L x (ℓ + 1) i =
        variance (fun θ => collectiveSigma Cb CW σ n ℓ (mlpZ Cb CW σ θ x ℓ))
          (stdGaussianParams n L)) := by sorry

end LesHouchesWidth
