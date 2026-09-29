-- Prove2me | Theorems.Thm_ModularCurve_deg_qInftyPlaceRat
-- name    : ModularCurve.deg_qInftyPlaceRat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/3b76fcf4-8eb2-53a2-8992-124ac050dd2a
-- title:
--   The q-adic place of a rational Laurent subfield has degree 1
-- statement:
--   Let $F$ be an intermediate field of the extension $\mathbb{Q} \subseteq \mathbb{Q}((q))$ of the field of formal Laurent series over $\mathbb{Q}$, and suppose that there is an element $j$ of $F$ whose image `qSeriesBar ℚ F j` in $\mathbb{Q}((q))$ has Hahn-series order exactly $-1$. Attached to these data is the place `qInftyPlaceRat F h` of $F$ over $\mathbb{Q}$, that is, the datum of the valuation subring `qIntegersBar ℚ F` of $F$ consisting of those $f \in F$ whose image in $\mathbb{Q}((q))$ has order $\geq 0$, together with the facts that this subring contains the image of $\mathbb{Q}$, is not all of $F$, and is a principal ideal ring (the last two being consequences of the existence of $j$). The theorem asserts that the degree of this place is $1$, the degree being by definition the $\mathbb{Q}$-dimension $\operatorname{finrank}_{\mathbb{Q}}$ of its residue field, the residue field of the local ring `qIntegersBar ℚ F`. Equivalently, the residue field at the cusp $q = 0$ is $\mathbb{Q}$ itself.
--
--   This records that the $q$-expansion place at infinity of a rational Laurent subfield is a rational place, in the sense of the degree theory of places of function fields. It is used in the computation of the degree of the cusp at infinity on the full modular curve, [`ModularCurve.deg_cuspInftyFull`](thm.html#ModularCurve.deg_cuspInftyFull).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_deg_qInftyPlaceRat.lean

import Definitions.Def_ModularCurve_QAdicPlace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve

theorem ModularCurve.deg_qInftyPlaceRat {F : IntermediateField ℚ (LaurentSeries ℚ)} (h : ∃ j : F, (qSeriesBar ℚ F j).order = -1) : (qInftyPlaceRat F h).deg = 1 := by sorry
