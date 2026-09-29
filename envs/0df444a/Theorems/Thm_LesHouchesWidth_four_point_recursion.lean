-- Prove2me | Theorems.Thm_LesHouchesWidth_four_point_recursion
-- name    : LesHouchesWidth.four_point_recursion
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T22:26:55.490153+00:00
-- url     : https://prove2.me/theorems/32a26244-8316-4c25-bfe9-35e17ecdc876
-- title:
--   Theorem 4.2: $\kappa_4=O(1/n)$ and its recursion up to $O(n^{-2})$
-- statement:
--   Fix $L\ge1$, $n_0,n_{L+1}\ge1$, $C_b\ge0$, $C_W>0$, a measurable polynomially bounded $\sigma$, and an input $x$ with $K^{(\ell)}>0$ for $1\le\ell\le L+1$. Fix $A\ge1$. Then there is a constant $C$ such that for every $n\ge1$ and all hidden widths with $n\le n_\ell\le An$ ($1\le\ell\le L$):
--
--   1. $|\kappa^{(\ell)}_4|\le C/n$ for $1\le\ell\le L+1$;
--   2. for $1\le\ell\le L$,
--   $$\Big|\kappa^{(\ell+1)}_4-\frac{C_W^2}{n_\ell}\mathrm{Var}_{K^{(\ell)}}\big[\sigma^2\big]-\big(\chi^{(\ell)}_\parallel\big)^2\kappa^{(\ell)}_4\Big|\le\frac{C}{n^2},$$
--   where $\mathrm{Var}_K[\sigma^2]=\langle\sigma^4\rangle_K-\langle\sigma^2\rangle_K^2$ and $\chi^{(\ell)}_\parallel=C_W\partial_K\langle\sigma^2\rangle_K|_{K=K^{(\ell)}}$.
--
--   This is the finite-width correction to the Gaussian-process limit: the four-point function is created at rate $1/n_\ell$ in each layer and propagated with factor $(\chi_\parallel)^2$.
--
--   **Formalization Note** "$n_1,\dots,n_L\simeq n$" is encoded as $n\le n_\ell\le An$. "Reasonable" $\sigma$ is taken to mean measurable and polynomially bounded. $C$ may depend on all fixed data but not on $n$ or the widths.
-- source:
--   Bahri, Hanin, Brossollet, Erba, Keup, Pacelli, Simon, *Les Houches Lectures on Deep Learning at Large & Infinite Width*, arXiv:2309.01592v3 (https://arxiv.org/abs/2309.01592), p. 33, Theorem 4.2 (first part), with the setting of Section 4.3.1 (p. 28) and Theorem 4.1 (pp. 31–32).

import Mathlib
import Definitions.Def_LesHouchesWidth_GaussianMLP
import Definitions.Def_LesHouchesWidth_FiniteWidth

namespace LesHouchesWidth

open MeasureTheory ProbabilityTheory

theorem four_point_recursion (Cb CW : ℝ) (hCb : 0 ≤ Cb) (hCW : 0 < CW)
    (σ : ℝ → ℝ) (hσ : Measurable σ) (hσ_poly : PolyBounded σ)
    (L : ℕ) (hL : 1 ≤ L) (n0 nOut : ℕ) (hn0 : 1 ≤ n0) (hnOut : 1 ≤ nOut) (x : Fin n0 → ℝ)
    (hK : ∀ ℓ ∈ Finset.Icc 1 (L + 1), 0 < nngpKernel Cb CW σ ℓ x x)
    (A : ℝ) (hA : 1 ≤ A) :
    ∃ C : ℝ, ∀ (N : ℕ) (n : ℕ → ℕ) (h0 : n 0 = n0), 1 ≤ N → n (L + 1) = nOut →
      (∀ ℓ ∈ Finset.Icc 1 L, N ≤ n ℓ ∧ (n ℓ : ℝ) ≤ A * N) →
      (∀ ℓ ∈ Finset.Icc 1 (L + 1), ∀ i : Fin (n ℓ),
        |kappa4 Cb CW σ n L (x ∘ Fin.cast h0) ℓ i| ≤ C / N) ∧
      (∀ ℓ ∈ Finset.Icc 1 L, ∀ (i : Fin (n (ℓ + 1))) (i' : Fin (n ℓ)),
        |kappa4 Cb CW σ n L (x ∘ Fin.cast h0) (ℓ + 1) i
          - CW ^ 2 / (n ℓ : ℝ) * gaussVarSq σ (nngpKernel Cb CW σ ℓ x x)
          - chiParallel CW σ (nngpKernel Cb CW σ ℓ x x) ^ 2 *
              kappa4 Cb CW σ n L (x ∘ Fin.cast h0) ℓ i'| ≤ C / (N : ℝ) ^ 2) := by sorry

end LesHouchesWidth
