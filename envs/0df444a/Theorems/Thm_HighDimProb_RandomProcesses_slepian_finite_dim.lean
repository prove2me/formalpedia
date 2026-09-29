-- Prove2me | Theorems.Thm_HighDimProb_RandomProcesses_slepian_finite_dim
-- name    : HighDimProb.RandomProcesses.slepian_finite_dim
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-19T22:57:52.530898+00:00
-- url     : https://prove2.me/theorems/d7271a4c-badb-45ee-b32a-f7f25893fdaf
-- title:
--   Theorem 7.2.9 — Slepian's inequality for Gaussian vectors
-- statement:
--   This is **Slepian's inequality**, stated for finite-dimensional Gaussian vectors — the form
--   Vershynin actually proves, using the technique of Gaussian interpolation, before extending it
--   to general Gaussian processes as Theorem 7.2.1.
--
--   Let $\iota$ be a finite, nonempty index set, and let $X, Y : \iota \to \mathbb R$ be two mean
--   zero Gaussian random vectors on a common probability space (i.e. every linear combination
--   $\sum_i a_i X_i$, resp. $\sum_i a_i Y_i$, is normal). Assume that for all $i,j \in \iota$,
--
--   $$
--   E X_i^2 = E Y_i^2 \qquad\text{and}\qquad E(X_i - X_j)^2 \le E(Y_i - Y_j)^2.
--   $$
--
--   Then for every $\tau \ge 0$,
--
--   $$
--   P\Bigl\{\max_{i} X_i \ge \tau\Bigr\} \;\le\; P\Bigl\{\max_{i} Y_i \ge \tau\Bigr\},
--   $$
--
--   and consequently $E\max_i X_i \le E\max_i Y_i$.
--
--   In words: if $X$ has the same "spread" as $Y$ coordinate-by-coordinate but grows at least as
--   fast in every pairwise increment, then $X$'s maximum stochastically dominates $Y$'s.
--
--   **Formalization Note** `IsGaussianProcess` (Mathlib) is used for "Gaussian vector/process":
--   every finite linear combination of coordinates is Gaussian, which for a finite index set is
--   exactly the book's Definition 7.1.10 applied to $\iota$ itself. The maximum is Mathlib's
--   `Finset.sup'` over `Finset.univ`, well-defined since `ι` is a nonempty `Fintype`.
-- source:
--   Vershynin, High-Dimensional Probability (2018), p. 164, Theorem 7.2.9

import Mathlib

open MeasureTheory ProbabilityTheory

namespace HighDimProb.RandomProcesses

/-- **Theorem 7.2.9** (Slepian's inequality, for Gaussian vectors), Vershynin,
*High-Dimensional Probability* (2018), p. 164 (PDF p. 172).

Let `X, Y : ι → Ω → ℝ` be two mean zero Gaussian random vectors indexed by a finite, nonempty
`ι` (i.e. Gaussian processes on `ι`, since `ι` is finite this is exactly a Gaussian vector in
`ℝ^ι`). Assume that for all `i, j ∈ ι`, `E Xᵢ² = E Yᵢ²` and `E(Xᵢ−Xⱼ)² ≤ E(Yᵢ−Yⱼ)²`. Then for
every `τ ≥ 0`, `P{maxᵢ Xᵢ ≥ τ} ≤ P{maxᵢ Yᵢ ≥ τ}`, and consequently `E maxᵢ Xᵢ ≤ E maxᵢ Yᵢ`. -/
theorem slepian_finite_dim :
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      {ι : Type} [Fintype ι] [Nonempty ι] (X Y : ι → Ω → ℝ)
      (hXG : IsGaussianProcess X P) (hYG : IsGaussianProcess Y P)
      (hXmean : ∀ i, ∫ ω, X i ω ∂P = 0) (hYmean : ∀ i, ∫ ω, Y i ω ∂P = 0)
      (hvar : ∀ i, ∫ ω, (X i ω) ^ 2 ∂P = ∫ ω, (Y i ω) ^ 2 ∂P)
      (hinc : ∀ i j, ∫ ω, (X i ω - X j ω) ^ 2 ∂P ≤ ∫ ω, (Y i ω - Y j ω) ^ 2 ∂P)
      (τ : ℝ), 0 ≤ τ →
      (P.real {ω | Finset.univ.sup' Finset.univ_nonempty (fun i => X i ω) ≥ τ} ≤
        P.real {ω | Finset.univ.sup' Finset.univ_nonempty (fun i => Y i ω) ≥ τ}) ∧
      ∫ ω, Finset.univ.sup' Finset.univ_nonempty (fun i => X i ω) ∂P ≤
        ∫ ω, Finset.univ.sup' Finset.univ_nonempty (fun i => Y i ω) ∂P := by sorry

end HighDimProb.RandomProcesses
