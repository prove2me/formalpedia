-- Prove2me | Theorems.Thm_GaussProcSparsify_Optimal_width_nonnegative_zero_iff
-- name    : GaussProcSparsify.Optimal.width_nonnegative_zero_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:53:46.374797+00:00
-- url     : https://prove2.me/theorems/394d5bdd-7615-4889-a940-1031d8a88d7f
-- title:
--   Section 2.2 — Gaussian width is nonnegative and vanishes exactly on singletons
-- statement:
--   Let $T\subseteq\mathbb R^n$ be nonempty. Its Gaussian width, possibly $+\infty$, satisfies
--   $$w(T)\ge0,\qquad w(T)=0\ \Longleftrightarrow\ \exists t\in\mathbb R^n,\ T=\{t\}.$$
--   This includes unbounded sets and dimension zero. It identifies exactly the zero-width case of the sparsification theorem; neither direction of the equivalence is omitted.
--
--   Differences from the source:
--   - encoding: $w(T)$ for a set $T$ → $T$ is nonempty; reason: the supremum over the empty set has no finite expected value and is outside the stated convention
--   - encoding: $w(T)=\mathbb E\sup_{t\in T}\langle g,t\rangle$ → extended-real expected supremum over finite nonempty marginals; reason: canonical sample paths are continuous and admit countable dense index sets, so the conventions agree; unbounded width remains infinite
--   - encoding: $\mathbb R^n$ with the Euclidean norm and standard Gaussian law → `EuclideanSpace ℝ (Fin n)` and `stdGaussian`, including $n=0$; reason: these give the same inner product, norm and Gaussian distribution
--   - encoding: $|T|=1$ → `∃ t, T = {t}`; reason: this says the same thing about a set
-- source:
--   Shivam Nadimpalli, Optimal Sparsification of Gaussian Processes, STOC 2027 submission #163 (October 2026), §2.2, PDF p. 13 (printed p. 12); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/163.pdf

import Mathlib
import Definitions.Def_GaussProcSparsify_Optimal_Gaussian

namespace GaussProcSparsify.Optimal

/-- §2.2, PDF p. 13. No boundedness is assumed: width may be +∞. -/
theorem width_nonnegative_zero_iff {n : ℕ} (T : Set (Vec n)) (hT : T.Nonempty) :
    0 ≤ gaussianWidth T ∧ (gaussianWidth T = 0 ↔ ∃ t : Vec n, T = {t}) := by sorry

end GaussProcSparsify.Optimal
