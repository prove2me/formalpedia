-- Prove2me | Theorems.Thm_ModularCurve_placeWidthChar_arithFrobC_smul
-- name    : ModularCurve.placeWidthChar_arithFrobC_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/9071775a-5bab-5a8d-a94b-839a60008171
-- title:
--   Frobenius invariance of the characteristic-q place width
-- statement:
--   Let $q$ be a prime, $N \ge 1$, and let $K$ be a perfect field of characteristic $q$. Write $F =$ `modularFunctionFieldC K N` for the intermediate field of the Laurent series field $K((T))$ generated over $K$ by the two series `jqModC K` and `jqNModC K N`, and let $w$ be a place of $F$ over $K$, i.e. a valuation subring of $F$ containing $\mathrm{algebraMap}\,K\,F$, distinct from $F$ itself, and a principal ideal ring. Let $g =$ `arithFrobC q K N` be the semilinear automorphism of $F/K$ given by the pair consisting of the coefficientwise $q$-power map on Laurent series and the Frobenius $x \mapsto x^q$ of $K$, acting on places by the pointwise action. The assertion is that the quantity `placeWidthChar q N` agrees at $g \cdot w$ and at $w$, where `placeWidthChar q N w` is the natural-number quotient of $w_{\mathrm{ch}} :=$ `jWidthChar q (w.evalAt (jGeomGen K N))` by `placeRamificationJ N w`; here `jGeomGen K N` is `jqModC K` regarded as an element of $F$, `w.evalAt f` is the residue of $f$ pulled back to $K$ if $f$ lies in the valuation subring and $0$ otherwise, `jWidthChar q j` equals $12$ or $1$ for $q = 2$ according as $j = 0$ or not, $6$ or $1$ for $q = 3$ according as $j = 0$ or not, and `jWidth j` for $q > 3$, and `placeRamificationJ N w` is the natural-number truncation of the order $w(\,$`jGeomGen K N`$-$`algebraMap K F (w.evalAt (jGeomGen K N))`$\,)$.
--
--   This is the characteristic-$q$ counterpart of the invariance of the width of a place of the level-$N$ modular function field under the arithmetic Frobenius of $K$, the width being normalised by the ramification index over the $j$-line. It is used in the comparison of the Hecke-torsion of the ribbon component group with a quotient of the character lattice in the supersingular-fibre analysis at level $N$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_placeWidthChar_arithFrobC_smul.lean

import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_CoeffSemilinearAut

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.placeWidthChar_arithFrobC_smul
    (q N : ℕ) [Fact q.Prime] [NeZero N]
    {K : Type*} [Field K] [CharP K q] [PerfectField K] [DecidableEq K]
    (w : Place K (modularFunctionFieldC K N)) :
    placeWidthChar q N (arithFrobC q K N • w) = placeWidthChar q N w := by sorry
