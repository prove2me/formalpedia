-- Prove2me | Theorems.Thm_Helfgott_finite_shell_weighted_integral_bound
-- name    : Helfgott.finite_shell_weighted_integral_bound
-- status  : Proved
-- author  : @flyingviper
-- created : 2026-11-11T00:17:06.753336+00:00
-- url     : https://prove2.me/theorems/d2c7777d-208e-4be3-884f-d3cbbb50c230
-- title:
--   Finite-shell weighted integral bound from cumulative energy
-- statement:
--   Let $(X,\mu)$ be a measure space and let $A_0,\ldots,A_N$ be pairwise disjoint measurable sets. Let $f,g:X\to\mathbb R$, assume that $f$ and $fg$ are integrable, and that $f\ge0$. Let the real weights satisfy
--
--   $$w_0\ge w_1\ge\cdots\ge w_N\ge0,\qquad g(x)\le w_i\quad(x\in A_i).$$
--
--   For real numbers $F_0,\ldots,F_N$, assume the cumulative energy bounds
--
--   $$\int_{A_0\cup\cdots\cup A_k} f\,d\mu\le F_k\qquad(0\le k\le N).$$
--
--   Then
--
--   $$\int_{A_0\cup\cdots\cup A_N}fg\,d\mu\le w_NF_N+\sum_{i=0}^{N-1}(w_i-w_{i+1})F_i.$$
--
--   This is a finite partition version of the summation-by-parts step in Helfgott's minor-arc argument. Taking the sets to be successive arc shells, $f$ to be squared exponential-sum magnitude, and $g$ to be the magnitude of the other exponential sum allows cumulative large-sieve bounds and decreasing pointwise bounds to be combined. It does not assert any numerical energy bound or complete the Goldbach minor-arc estimate. The case $N=0$ is included; neither the measure space nor the total measure needs to be finite.
-- source:
--   H. A. Helfgott, The ternary Goldbach conjecture is true, arXiv:1312.7748v2, Section 6.1, Lemma 6.1 (the finite inequality immediately following equation (6.2)) and the shell decomposition in the proof of Proposition 6.2, equations (6.4)-(6.8). https://arxiv.org/html/1312.7748v2 . This formulation retains the finite Abel sum rather than replacing it with a derivative integral, and states the measure-space generality used by that step.

import Mathlib.Algebra.BigOperators.Module
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open MeasureTheory Finset
open scoped BigOperators

theorem Helfgott.finite_shell_weighted_integral_bound {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (N : ℕ) (s : ℕ → Set α) (f g : α → ℝ) (w F : ℕ → ℝ)
    (hs : ∀ i ≤ N, MeasurableSet (s i))
    (hdisj : Set.PairwiseDisjoint (↑(range (N + 1)) : Set ℕ) s)
    (hf : Integrable f μ) (hfg : Integrable (fun x => f x * g x) μ)
    (hf0 : ∀ x, 0 ≤ f x)
    (hg : ∀ i ≤ N, ∀ x ∈ s i, g x ≤ w i)
    (hw : ∀ i < N, w (i + 1) ≤ w i) (hwN : 0 ≤ w N)
    (hF : ∀ k ≤ N,
      (∫ x in ⋃ i ∈ range (k + 1), s i, f x ∂μ) ≤ F k) :
    (∫ x in ⋃ i ∈ range (N + 1), s i, f x * g x ∂μ) ≤
      w N * F N + ∑ i ∈ range N, (w i - w (i + 1)) * F i := by sorry
