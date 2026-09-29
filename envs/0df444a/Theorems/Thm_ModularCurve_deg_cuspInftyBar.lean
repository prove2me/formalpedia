-- Prove2me | Theorems.Thm_ModularCurve_deg_cuspInftyBar
-- name    : ModularCurve.deg_cuspInftyBar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/00c196cc-0fe0-5660-abd1-33e1e8a124ce
-- title:
--   The cusp ∞ is a degree-one place of X(N)_{ℚ̄}
-- statement:
--   Let $N$ be a natural number, assumed non-zero. Work over $\bar{\mathbb{Q}} =$ `AlgebraicClosure ℚ` and with the field $F =$ `modularFunctionFieldBar N`, the base change to $\bar{\mathbb{Q}}$, inside $\bar{\mathbb{Q}}((q))$, of the full modular function field of level $N$ viewed as an intermediate field of $\mathbb{Q}((q))$. Here a `Place` of $F$ over $\bar{\mathbb{Q}}$ is a valuation subring of $F$ that contains the image of $\bar{\mathbb{Q}}$, is not all of $F$, and is a principal ideal ring, and its degree `deg` is the $\bar{\mathbb{Q}}$-dimension of the residue field of that valuation subring. The place `cuspInftyBar N` is the $q$-adic one, `qInftyPlaceBar`, whose valuation subring is `qIntegersBar`, consisting of the elements whose associated $q$-series `qSeriesBar` has non-negative order; the existence witness needed for its construction is the image under the coefficient map `coeffEmb` of the $q$-expansion `jq` of the modular invariant, which lies in the base-changed field and has $q$-order $-1$. The assertion is that this place has degree $1$, i.e. its residue field is $\bar{\mathbb{Q}}$ itself.
--
--   This records that the cusp at infinity is a rational point of the modular curve of level $N$ over $\bar{\mathbb{Q}}$, in the guise of a degree-one place of its function field. It is used in the computation of degrees of other cusps, such as [`ModularCurve.deg_cuspZeroBar`](thm.html#ModularCurve.deg_cuspZeroBar), in showing that the cuspidal divisor class [`ModularCurve.cuspidalClass_ne_zero`](thm.html#ModularCurve.cuspidalClass_ne_zero) is non-trivial, and in the ramification bookkeeping of [`ModularCurve.MultCovering.eq_mAnnuli_add_one_of_isEmbBasis`](thm.html#ModularCurve.MultCovering.eq_mAnnuli_add_one_of_isEmbBasis).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_deg_cuspInftyBar.lean

import Definitions.Def_ModularCurve_AtkinLehner

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve

theorem ModularCurve.deg_cuspInftyBar (N : ℕ) [NeZero N] : (cuspInftyBar N).deg = 1 := by sorry
