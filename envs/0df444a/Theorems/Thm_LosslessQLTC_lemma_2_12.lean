-- Prove2me | Theorems.Thm_LosslessQLTC_lemma_2_12
-- name    : LosslessQLTC.lemma_2_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:20:09.331972+00:00
-- url     : https://prove2.me/theorems/87406f0f-21c0-4eac-bd6c-9a75aa85b562
-- title:
--   Lemma 2.12, p.18 — boundary maps of $X$ are coboundary maps of $X^{\mathrm{rev}}$
-- statement:
--   For $0\le s\le k$, the identity on functions identifies $C_s(X)$ with $C^{k-s}(X^{\mathrm{rev}})$. Under this identification, for $1\le s\le k$,
--
--   $$\partial_s^X=\delta_{k-s}^{X^{\mathrm{rev}}}.$$
--
--   Moreover $D_i^{\mathrm{rev}}=D'_i$ and $(D'_i)^{\mathrm{rev}}=D_i$. This lets every result about coboundaries of $X^{\mathrm{rev}}$ be read as a result about the boundary maps of $X$.
--
--   Differences from the source:
--   - encoding: a decorated $(k,2)$-cubical complex with blocks $V_I$ and cubes $X(i)$ for all $i$, directions $1,\dots,k$ → `SquareComplex k`: one vertex type with a type map, the graph and $X(2)$ only, directions `Fin k`; reason: $X(0),X(1)$ are forced, no result uses $X(i)$ for $i\ge3$, and any such data extends with $X(i)=\emptyset$ for $i\ge3$
--   - encoding: $\partial_s^X=\delta_{k-s}^{X^{\mathrm{rev}}}$ with $k-s$ → an explicit equivalence `revLevel X s t h` for $s+t=k$, equal to the identity on vertices; `partialMap X s` is $\partial_{s+1}$; reason: avoids natural-number subtraction and casts; same maps
-- source:
--   Cohen, Leigh, Reiner, Ta-Shma, Tzalik, Good Quantum Locally Testable Codes from Lossless Cubical Complexes, arXiv:2610.00525 (held version, sha256 d61f0ed9…), Lemma 2.12, p.18

import Mathlib
import Definitions.Def_LosslessQLTC_rev

namespace LosslessQLTC

/-- Lemma 2.12 (arXiv:2610.00525, held version, sha256 d61f0ed9…, p.18): the identity on functions
identifies `C_s(X)` with `C^{k−s}(X^rev)`, under this identification `∂_s^X = δ_{k−s}^{X^rev}`
for `1 ≤ s ≤ k`, and `D_i^rev = D′_i`, `(D′_i)^rev = D_i`.

**Formalization Note.** `revLevel X s t h` is the identification, for `s + t = k`; its first clause
says it is the identity on vertices. `partialMap X s` is the source's `∂_{s+1}`, so the case `s + 1`
of the source has `t = k − (s + 1)`, i.e. `s + 1 + t = k`. That `X^rev` is again a square complex
is the fact that `rev X` has type `SquareComplex k`. -/
theorem lemma_2_12 {k : ℕ} (X : SquareComplex k) :
    (∀ (s t : ℕ) (h : s + t = k) (v : Level X s), (revLevel X s t h v).1 = v.1) ∧
    (∀ (s t : ℕ) (h : s + 1 + t = k) (f : Level X (s + 1) → ZMod 2) (u : Level X s),
      partialMap X s f u =
        delta (rev X) t (f ∘ (revLevel X (s + 1) t h).symm)
          (revLevel X s (t + 1) (by omega) u)) ∧
    (rev X).D = X.D' ∧ (rev X).D' = X.D := by sorry

end LosslessQLTC
