-- Prove2me | Theorems.Thm_LesHouchesWidth_finite_width_expansion
-- name    : LesHouchesWidth.finite_width_expansion
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-23T22:20:38.626643+00:00
-- url     : https://prove2.me/theorems/caa39bd8-3a96-4e34-8771-028fcdc2fa94
-- title:
--   Theorem 4.2: $1/n$ expansion of expectations of observables of $m$ neurons
-- statement:
--   Under the hypotheses of the recursion (Theorem 4.2), fix $m\ge1$ and a smooth $f:\mathbb R^m\to\mathbb R$ all of whose derivatives are polynomially bounded. Then there is $C$ such that for every $n\ge1$, all hidden widths with $n\le n_\ell\le An$, every layer $1\le\ell\le L+1$ with $n_\ell\ge m$,
--   $$\Big|\mathbb E\,f\big(z^{(\ell)}_1,\dots,z^{(\ell)}_m\big)-\langle f\rangle_{G^{(\ell)}}-\frac{\kappa^{(\ell)}_4}{8}\Big\langle\Big(\sum_{j=1}^m\partial_j^4+\sum_{j_1\neq j_2}\partial_{j_1}^2\partial_{j_2}^2\Big)f\Big\rangle_{K^{(\ell)}}\Big|\le\frac{C}{n^2},$$
--   where $\langle\cdot\rangle_K$ denotes the average against $m$ i.i.d. $\mathcal N(0,K)$ variables and $G^{(\ell)}=\mathbb E[(z^{(\ell)}_1)^2]$ is the dressed two-point function.
--
--   To order $1/n$, all single-input statistics of a layer are determined by its two-point function and $\kappa_4$.
--
--   **Formalization Note** The notes print $\kappa^{(\ell+1)}_4$ in front of the correction term. This appears to be an index slip: with $\kappa^{(\ell)}_4$ the formula is exact for $f=z_1^4$ and $f=z_1^2z_2^2$. "Reasonable" $f$ is taken to be smooth with polynomially bounded derivatives.
-- source:
--   Bahri, Hanin, Brossollet, Erba, Keup, Pacelli, Simon, *Les Houches Lectures on Deep Learning at Large & Infinite Width*, arXiv:2309.01592v3 (https://arxiv.org/abs/2309.01592), p. 33, Theorem 4.2 ("Moreover, for any fix $m\ge1$ and any 'reasonable' function $f$ ...").

import Mathlib
import Definitions.Def_LesHouchesWidth_GaussianMLP
import Definitions.Def_LesHouchesWidth_FiniteWidth

namespace LesHouchesWidth

open MeasureTheory ProbabilityTheory

theorem finite_width_expansion (Cb CW : ℝ) (hCb : 0 ≤ Cb) (hCW : 0 < CW)
    (σ : ℝ → ℝ) (hσ : Measurable σ) (hσ_poly : PolyBounded σ)
    (L : ℕ) (hL : 1 ≤ L) (n0 nOut : ℕ) (hn0 : 1 ≤ n0) (hnOut : 1 ≤ nOut) (x : Fin n0 → ℝ)
    (hK : ∀ ℓ ∈ Finset.Icc 1 (L + 1), 0 < nngpKernel Cb CW σ ℓ x x)
    (A : ℝ) (hA : 1 ≤ A) (m : ℕ) (hm : 1 ≤ m) (f : (Fin m → ℝ) → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hf_poly : ∀ k : ℕ, ∃ Cf : ℝ, ∃ p : ℕ, ∀ y, ‖iteratedFDeriv ℝ k f y‖ ≤ Cf * (1 + ‖y‖ ^ p)) :
    ∃ C : ℝ, ∀ (N : ℕ) (n : ℕ → ℕ) (h0 : n 0 = n0), 1 ≤ N → n (L + 1) = nOut →
      (∀ ℓ ∈ Finset.Icc 1 L, N ≤ n ℓ ∧ (n ℓ : ℝ) ≤ A * N) →
      ∀ ℓ ∈ Finset.Icc 1 (L + 1), ∀ hmℓ : m ≤ n ℓ,
        |∫ θ, f (fun j => mlpZ Cb CW σ θ (x ∘ Fin.cast h0) ℓ (Fin.castLE hmℓ j))
              ∂(stdGaussianParams n L)
          - gaussAvgVec m
              (dressedTwoPoint Cb CW σ n L (x ∘ Fin.cast h0) ℓ (Fin.castLE hmℓ ⟨0, hm⟩)) f
          - kappa4 Cb CW σ n L (x ∘ Fin.cast h0) ℓ (Fin.castLE hmℓ ⟨0, hm⟩) / 8 *
              gaussAvgVec m (nngpKernel Cb CW σ ℓ x x) (fun y =>
                ∑ j : Fin m, iteratedFDeriv ℝ 4 f y (fun _ => Pi.single j 1) +
                ∑ j₁ : Fin m, ∑ j₂ : Fin m, if j₁ = j₂ then 0 else
                  iteratedFDeriv ℝ 4 f y
                    ![Pi.single j₁ 1, Pi.single j₁ 1, Pi.single j₂ 1, Pi.single j₂ 1])|
          ≤ C / (N : ℝ) ^ 2 := by sorry

end LesHouchesWidth
