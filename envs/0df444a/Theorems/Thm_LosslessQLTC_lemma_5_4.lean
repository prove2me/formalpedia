-- Prove2me | Theorems.Thm_LosslessQLTC_lemma_5_4
-- name    : LosslessQLTC.lemma_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:23:45.57046+00:00
-- url     : https://prove2.me/theorems/70b9ab01-28fe-4d51-a917-cc97e3adf317
-- title:
--   Lemma 5.4, p.41 — Algorithm 1 stops and returns a locally minimal cochain
-- statement:
--   For an input cochain $f\in C^i(X)$, $1\le i\le k$, Algorithm 1 stops after at most $D_{[k]}\cdot\|f\|$ iterations and returns a locally minimal cochain. Since the algorithm's choices are free, the iteration bound holds for every run, a run that stops exists, and any cochain at which no iteration is available is locally minimal. This is how the expansion theorem, which concerns locally minimal cochains, is applied to arbitrary words.
--
--   Differences from the source:
--   - encoding: a decorated $(k,2)$-cubical complex with blocks $V_I$ and cubes $X(i)$ for all $i$, directions $1,\dots,k$ → `SquareComplex k`: one vertex type with a type map, the graph and $X(2)$ only, directions `Fin k`; reason: $X(0),X(1)$ are forced, no result uses $X(i)$ for $i\ge3$, and any such data extends with $X(i)=\emptyset$ for $i\ge3$
--   - reading: the nondeterministic Algorithm 1 stops after at most $D_{[k]}\|f\|$ iterations and returns a locally minimal cochain → the bound holds for every run, a stopping run exists, and any state with no available iteration is locally minimal; reason: this is the meaning of the statement for a nondeterministic procedure, and it is what the proof gives
-- source:
--   Cohen, Leigh, Reiner, Ta-Shma, Tzalik, Good Quantum Locally Testable Codes from Lossless Cubical Complexes, arXiv:2610.00525 (held version, sha256 d61f0ed9…), Lemma 5.4, p.41

import Mathlib
import Definitions.Def_LosslessQLTC_Greedy

namespace LosslessQLTC

/-- Lemma 5.4 (arXiv:2610.00525, held version, sha256 d61f0ed9…, p.41): for an input cochain `f`,
Algorithm 1 stops after at most `D_{[k]} · ∥f∥` iterations and returns a locally-minimal cochain.

**Formalization Note.** The algorithm is nondeterministic, so the bound is for every run. The second
clause says a run that stops exists (which also follows from the first, as the norm decreases), and
the third that any state from which no iteration is available is locally minimal. The input level
is `i = q + 1`, so `1 ≤ i ≤ k` is `q + 1 ≤ k`. -/
theorem lemma_5_4 {k : ℕ} (X : SquareComplex k) (q : ℕ) (hq : q + 1 ≤ k)
    (f : Level X (q + 1) → ZMod 2) :
    (∀ (n : ℕ) (g : Level X (q + 1) → ZMod 2), GreedyRun X q n f g →
      (n : ℝ) ≤ (prodD X.D Finset.univ : ℝ) * normC X f) ∧
    (∃ (n : ℕ) (g : Level X (q + 1) → ZMod 2), GreedyRun X q n f g ∧
      ∀ g', ¬ GreedyStep X q g g') ∧
    (∀ g : Level X (q + 1) → ZMod 2, (∀ g', ¬ GreedyStep X q g g') →
      IsLocallyMinimal X (q + 1) g) := by sorry

end LosslessQLTC
