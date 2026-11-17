-- Prove2me | Theorems.Thm_NadlerCLS_Supplement_theorem_5_1
-- name    : NadlerCLS.Supplement.theorem_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T01:56:04.173201+00:00
-- url     : https://prove2.me/theorems/3ca2bd79-60cb-444d-9999-c529c6e60124
-- title:
--   Theorem 5.1 — LARGE-MARGIN-TRIPLET-FOSP reduces to $1$-Projected-Nadler
-- statement:
--   There is a polynomial-time many-one search reduction
--
--   $$
--   \text{LARGE-MARGIN-TRIPLET-FOSP}\ \le_p\ 1\text{-Projected-Nadler}.
--   $$
--
--   The source is Definition 3 in full: rational positive triplet weights, a rational margin $\alpha\ge d_{\mathrm{emb}}$ including equality, arbitrary rational accuracy $\varepsilon>0$, and the variational inequality against every point of $[0,1]^{d_{\mathrm{emb}}|V|}$. The target exponent is fixed to $\beta=1$, while its dimension is encoded in the instance and may grow polynomially with the source input. The reduction has a polynomial-time instance map and a polynomial-time decoder that converts every valid target answer into a source FOSP.
--
--   This supplies the CLS-membership reduction for large-margin triplet-loss stationarity.
--
--   Differences from the source:
--   - encoding: a finite set $V$, ordered triplet collection, and points in the box → movable labels are `Fin v`, the collection is a list, coordinates are 0-based, and answers are rational vectors with binary codes; reason: every finite labeled instance has this representation, repetitions combine through their weights, and the paper's computational model uses rational binary data
--   - encoding: polynomial-dimensional $\beta$-Projected-Nadler → a self-delimiting dimension tag followed by the published `pnSearch n 1` payload and its unchanged (N1)–(N4) answers; reason: this is the disjoint union over all dimensions and preserves the paper's varying target dimension rather than fixing $n=3$
-- source:
--   Xiong–Vlatakis-Gkaragkounis, On the Complexity of Finding Fixed Points for Set-Valued Contractions, arXiv:2609.14101 (held version of 2026-11-03, sha256 1fcc5a027ffe65205e4ef9a9ef7730f6f07fe3f7006447cac39a7562e36dc485), Theorem 5.1, p.14; Definition 3, pp.13–14; proof pp.57–58

import Mathlib
import Definitions.Def_CardinalMatching_SearchReduces
import Definitions.Def_NadlerCLS_Supplement_LMTripletInstance
import Definitions.Def_NadlerCLS_Supplement_variablePnSearch

set_option autoImplicit false

namespace NadlerCLS

namespace Supplement

open CardinalMatching

/-- **Theorem 5.1.** There is a polynomial-time many-one search reduction from
LARGE-MARGIN-TRIPLET-FOSP to `β`-Projected-Nadler with the fixed parameter `β = 1`.
(Xiong–Vlatakis-Gkaragkounis, *On the Complexity of Finding Fixed Points for Set-Valued
Contractions*, arXiv:2609.14101, held version of 2026-11-03, sha256
1fcc5a02…6dc485, Theorem 5.1, p.14; proof, pp.57–58.)

**Formalization Note** The source search problem is Definition 3 in full: rational positive
weights, `alpha ≥ d` (including equality), arbitrary positive rational accuracy, and the exact
variational inequality for every point of the box.  Its `v = 0` instances have a zero-dimensional
answer.  The target is `variablePnSearch 1`, the dimension-tagged aggregate of the published
`pnSearch n 1`; it is not the three-dimensional problem used in Theorem 3.2.  `SearchReduces`
requires polynomial-time instance and answer maps and correctness for every target answer. -/
theorem theorem_5_1 :
    SearchReduces largeMarginTripletFOSPSearch (variablePnSearch 1) := by sorry

end Supplement

end NadlerCLS
