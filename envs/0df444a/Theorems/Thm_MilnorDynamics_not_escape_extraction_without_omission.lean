-- Prove2me | Theorems.Thm_MilnorDynamics_not_escape_extraction_without_omission
-- name    : MilnorDynamics.not_escape_extraction_without_omission
-- status  : Open
-- author  : @WillR
-- created : 2026-10-02T09:42:51.145392+00:00
-- url     : https://prove2.me/theorems/bef258d3-c52d-4aa5-a364-c8ee96bf1bb9
-- title:
--   Escape extraction from pointwise unboundedness alone is false: the omitted-values hypothesis is load-bearing
-- statement:
--   **Counterexample to the unconditional extraction step.**
--
--   Suppose one tries to prove Milnor's per-compact escape statement `exists_subseq_escapes_on_compacts` by splitting it into an analytic rigidity half and a combinatorial extraction half, where the combinatorial half uses only continuity on the compact together with unboundedness at one point. That split is invalid: the extraction assertion is false by itself.
--
--   Take $U=\mathbb C$, $K=[0,1]$, $z_0=0$, and $f_n(z)=n-n^2 z$. Each $f_n$ is a polynomial and so continuous (indeed holomorphic) on $U$; $z_0\in K$ is compact in $U$; and $\|f_n(z_0)\|=n$, so the family is unbounded at $z_0$. Nevertheless $f_n(1/n)=0$, so for $R=1$ the set of indices with $|f_n(z)|>1$ for every $z\in K$ is empty, and no subsequence escapes on $K$.
--
--   Strengthening unboundedness at one point to unboundedness at every point does not help: for every fixed $z>0$ one has $|f_n z|=n|nz-1|\to\infty$, so the family is unbounded at every point of $K$ and still no subsequence escapes.
--
--   This family is excluded from the leaf only because it attains the omitted value $0$. The consequence is that the omitted-values hypothesis is load-bearing in **both** halves of the proposed decomposition, so `exists_subseq_escapes_on_compacts` admits no unconditional combinatorial child and its analytic content cannot be packaged away.
-- source:
--   Milnor, Dynamics in One Complex Variable, 3rd ed., Chapter 3, the escape step in the proof of Montel's theorem; the obstruction recorded here is a standard normal-family example and is what forces the two-constants (Schottky) input into the proof of Zalcwasser's theorem.

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies

open scoped OnePoint
open Filter Set

namespace MilnorDynamics

/-- **Escape extraction genuinely needs the omitted-values hypothesis.**

The informal plan for `exists_subseq_escapes_on_compacts` is to split it into an
"analytic rigidity" half and a "combinatorial extraction" half, where the
combinatorial half would use only continuity on the compact plus unboundedness at
one point.  That split is **not valid**: the extraction statement is false on its
own.

Counterexample: take `U = ℂ` (or the open unit disc), `K = [0, 1]`, `z0 = 0`, and
`f n z = n - n^2 * z`.  Each `f n` is a polynomial, hence continuous (indeed
holomorphic) on `U`, and `||f n z0|| = n`, so the family is unbounded at `z0`.
But `f n (1 / n) = 0`, so no subsequence escapes `R = 1` on `K`.  Moreover
`||f n z|| = n |n z - 1|`, which tends to infinity for each fixed `z > 0`, so
the family is unbounded at *every* point of `K` and still no subsequence escapes.

The counterexample is excluded from the leaf only because its members hit `0`.
Hence the omitted-values hypothesis is load-bearing in **both** halves of the
proposed split, and `exists_subseq_escapes_on_compacts` cannot be decomposed
into an unconditional combinatorial child. -/
theorem not_escape_extraction_without_omission :
    ¬ (∀ (U : Set ℂ) (f : ℕ → ℂ → ℂ), (∀ n, ContinuousOn (f n) U) →
        (∀ K : Set ℂ, K ⊆ U → IsCompact K →
          ∀ z₀ : ℂ, z₀ ∈ K →
            (∀ M : ℝ, ∃ n, M < ‖f n z₀‖) →
            ∃ φ : ℕ → ℕ, StrictMono φ ∧
              ∀ R : ℝ, ∀ᶠ n in atTop, ∀ z ∈ K, R < ‖f (φ n) z‖)) := by sorry

end MilnorDynamics
