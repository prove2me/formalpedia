-- Prove2me | Theorems.Thm_LosslessQLTC_lemma_2_10
-- name    : LosslessQLTC.lemma_2_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:12:00.454778+00:00
-- url     : https://prove2.me/theorems/146f6a1d-a432-418b-bef4-68a129b07300
-- title:
--   Lemma 2.10, p.17 — $\partial^2=0$ and $\delta^2=0$
-- statement:
--   Let $X$ be a $(k,2)$-cubical complex and let $1\le s\le k-1$. Then
--
--   $$\partial_s\partial_{s+1}=0,\qquad\delta_s\delta_{s-1}=0.$$
--
--   So the levels of $X$ form a chain complex over $\mathbb F_2$, which is what makes the level complex a CSS code.
--
--   Differences from the source:
--   - encoding: a decorated $(k,2)$-cubical complex with blocks $V_I$ and cubes $X(i)$ for all $i$, directions $1,\dots,k$ → `SquareComplex k`: one vertex type with a type map, the graph and $X(2)$ only, directions `Fin k`; reason: $X(0),X(1)$ are forced, no result uses $X(i)$ for $i\ge3$, and any such data extends with $X(i)=\emptyset$ for $i\ge3$
--   - encoding: $\partial_s$, for $1\le s\le k$ → `partialMap X (s-1)`, indexed by its target; $s=q+1$; reason: avoids natural-number subtraction; same maps
--   - reading: every $(k,2)$-cubical complex, with the biregularity assumption printed on p.17 just after the lemma → `SquareComplex k` carries the $(D_i,D'_i)$-biregularity with $D_i,D'_i>0$; reason: p.17 states this assumption "throughout", for the whole paper, and every complex the paper uses satisfies it; the proof of the lemma does not use it
-- source:
--   Cohen, Leigh, Reiner, Ta-Shma, Tzalik, Good Quantum Locally Testable Codes from Lossless Cubical Complexes, arXiv:2610.00525 (held version, sha256 d61f0ed9…), Lemma 2.10, p.17

import Mathlib
import Definitions.Def_LosslessQLTC_Level

namespace LosslessQLTC

/-- Lemma 2.10 (Cohen, Leigh, Reiner, Ta-Shma, Tzalik, arXiv:2610.00525, held version, sha256
d61f0ed9…, p.17): for every `(k, 2)`-cubical complex and `1 ≤ s ≤ k − 1`, `∂_s ∂_{s+1} = 0` and
`δ_s δ_{s−1} = 0`.

**Formalization Note.** `s = q + 1`, and `partialMap X q` is the source's `∂_{q+1}`. -/
theorem lemma_2_10 {k : ℕ} (X : SquareComplex k) (q : ℕ) (hq : q + 2 ≤ k) :
    partialMap X q ∘ₗ partialMap X (q + 1) = 0 ∧ delta X (q + 1) ∘ₗ delta X q = 0 := by sorry

end LosslessQLTC
