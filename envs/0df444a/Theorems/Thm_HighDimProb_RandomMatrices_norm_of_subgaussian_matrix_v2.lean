-- Prove2me | Theorems.Thm_HighDimProb_RandomMatrices_norm_of_subgaussian_matrix_v2
-- name    : HighDimProb.RandomMatrices.norm_of_subgaussian_matrix_v2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-10-06T06:20:13.046985+00:00
-- url     : https://prove2.me/theorems/7f8788fe-9e82-44b3-9959-c0a196a19805
-- title:
--   Theorem 4.4.5 — Norm of matrices with sub-gaussian entries: $\|A\| \le CK(\sqrt m+\sqrt n+t)$ w.p. $\ge 1-2e^{-t^2}$
-- statement:
--   This is **Theorem 4.4.5**, the goal theorem of this mission: the first non-asymptotic bound on the operator norm of a random matrix, obtained by the $\varepsilon$-net argument (small nets of the unit spheres from Corollary 4.2.13, the reduction of the operator norm to a supremum over nets from Exercise 4.4.3, a union bound over the nets combined with the sub-gaussian tail of each fixed quadratic form $\langle Ax,y\rangle$).
--
--   There is an absolute constant $C>0$ such that the following holds. Let $A$ be an $m\times n$ random matrix whose entries $A_{ij}$ are independent, mean-zero, sub-gaussian random variables, and let $K\ge \max_{i,j}\|A_{ij}\|_{\psi_2}$, where $\|\cdot\|_{\psi_2}$ is the sub-gaussian norm (companion definition `HighDimProb.Concentration.subgaussianNorm`, now valued in $[0,\infty]$ with $\|X\|_{\psi_2}<\infty$ iff $X$ is sub-gaussian). Then, for any $t>0$,
--   $$
--   \mathrm{Prob}\bigl\{\|A\|\le CK(\sqrt m+\sqrt n+t)\bigr\}\;\ge\;1-2\exp(-t^2),
--   $$
--   where $\|A\|$ is the operator norm (companion definition `matrixOpNorm`).
--
--   **Formalization Note.** The retired version was disproved because its real-valued sub-gaussian norm returned the junk value $0$ for a non-sub-gaussian entry and its mean-zero hypothesis was a bare Bochner integral (also $0$ for a non-integrable entry), so the entry $\omega\mapsto\omega^{-1}$ on $(0,1]$ satisfied every hypothesis with $K=0$. The new statement uses the corrected `ℝ≥0∞`-valued norm with $K\in[0,\infty)$ (`ℝ≥0`), so the hypothesis $\|A_{ij}\|_{\psi_2}\le K$ now says exactly that every entry is sub-gaussian with norm at most $K$ — the book's "sub-gaussian random variables" with "$K=\max_{i,j}\|A_{ij}\|_{\psi_2}$" (any upper bound $K$ is what the proof uses) — and states mean zero as $A_{ij}$ integrable with $\mathbb E A_{ij}=0$ (integrability is implied by sub-gaussianity and is written only to make the expectation genuine). Conventions made explicit: $C$ is existentially quantified before every other object, matching the book's "absolute constant"; independence of the $mn$ entries is `iIndepFun` over $\mathrm{Fin}\,m\times\mathrm{Fin}\,n$; $m,n\ge1$ as for any $m\times n$ matrix; $t>0$ as in "for any $t>0$". Edge cases: $K=0$ forces every entry to vanish almost surely and the event has probability $1$.
-- source:
--   Vershynin, High-Dimensional Probability (CUP 2018), Theorem 4.4.5, p. 91 (PDF p. 99); sub-gaussian norm Definition 2.5.6, Eq. (2.13), p. 28

import Mathlib
import Definitions.Def_HighDimProb_Concentration_SubgaussianNorm_v2
import Definitions.Def_HighDimProb_RandomMatrices_matrixOpNorm

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace HighDimProb.RandomMatrices

/-- **Theorem 4.4.5** (Norm of matrices with sub-gaussian entries), Vershynin,
*High-Dimensional Probability* (2018), p. 91.

Let `A` be an `m × n` random matrix whose entries `Aᵢⱼ` are independent, mean zero,
sub-gaussian random variables. Then, for any `t > 0`, `‖A‖ ≤ CK(√m + √n + t)` with
probability at least `1 − 2exp(−t²)`, where `K = maxᵢ,ⱼ ‖Aᵢⱼ‖ψ2`.

Corrected version (`_v2`): the sub-gaussian norm is the corrected `ℝ≥0∞`-valued
`HighDimProb.Concentration.subgaussianNorm` (`⊤` for a non-sub-gaussian entry), and `K : ℝ≥0`,
so `‖Aᵢⱼ‖_{ψ₂} ≤ K` now states that every entry *is* sub-gaussian with norm at most `K`. The
retired version's real-valued norm returned `0` on a non-sub-gaussian entry, and its mean-zero
hypothesis was a bare Bochner integral (`0` for a non-integrable entry), so a non-integrable
entry satisfied every hypothesis with `K = 0`. Mean zero is now `Integrable ∧ ∫ = 0` (the
integrability is implied by sub-gaussianity and is stated only to make the expectation
genuine). -/
theorem norm_of_subgaussian_matrix_v2 :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (Prob : Measure Ω) [IsProbabilityMeasure Prob]
        {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (A : Ω → Matrix (Fin m) (Fin n) ℝ)
        (hindep : iIndepFun (fun p : Fin m × Fin n => fun ω => A ω p.1 p.2) Prob)
        (hmean : ∀ i j, Integrable (fun ω => A ω i j) Prob ∧ ∫ ω, A ω i j ∂Prob = 0)
        (K : ℝ≥0)
        (hK : ∀ i j, HighDimProb.Concentration.subgaussianNorm Prob (fun ω => A ω i j) ≤ K)
        (t : ℝ) (ht : 0 < t),
        1 - 2 * Real.exp (-(t ^ 2)) ≤
          Prob.real {ω | matrixOpNorm (A ω) ≤ C * K * (Real.sqrt m + Real.sqrt n + t)} := by sorry

end HighDimProb.RandomMatrices
