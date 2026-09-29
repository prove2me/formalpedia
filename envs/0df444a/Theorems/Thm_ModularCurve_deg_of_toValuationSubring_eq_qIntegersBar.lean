-- Prove2me | Theorems.Thm_ModularCurve_deg_of_toValuationSubring_eq_qIntegersBar
-- name    : ModularCurve.deg_of_toValuationSubring_eq_qIntegersBar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/099cf7df-49d6-5b0d-bec0-de86c6793ed1
-- title:
--   The q-adic place of a subfield of ℚ((q)) has degree 1
-- statement:
--   Let $F$ be an intermediate field of the extension $\mathbb{Q}((q))/\mathbb{Q}$, equipped with some $\mathbb{Q}$-algebra structure, and assume that $F$ contains an element $j$ whose image in $\mathbb{Q}((q))$ has Hahn-series order exactly $-1$. Let $v$ be a place of $F$ over $\mathbb{Q}$ in the sense of the project's structure `Place`: a valuation subring of $F$ that contains the image of $\mathbb{Q}$ under the algebra map, is not all of $F$, and is a principal ideal ring. Suppose that the valuation subring underlying $v$ is `qIntegersBar ℚ F`, namely the subring of those $f \in F$ whose image in $\mathbb{Q}((q))$ has order $\ge 0$. Then $v.\mathrm{deg} = 1$, where the degree of $v$ is by definition the $\mathbb{Q}$-dimension of the residue field of its valuation subring; that is, the residue field of the $q$-adic place of $F$ is $\mathbb{Q}$ itself.
--
--   This identifies the cusp $q = 0$ as a rational point: the $q$-adic place of a function field realised inside $\mathbb{Q}((q))$ by $q$-expansions is a place of residue degree $1$ over $\mathbb{Q}$. It is used in the treatment of the rational modular curves, where it is invoked through [`ModularCurve.deg_qInftyPlaceRat`](thm.html#ModularCurve.deg_qInftyPlaceRat), the hypothesis being given in the form 'the valuation ring of $v$ consists of the $q$-expansions with no pole'.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_deg_of_toValuationSubring_eq_qIntegersBar.lean

import Definitions.Def_ModularCurve_QAdicPlace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve

theorem ModularCurve.deg_of_toValuationSubring_eq_qIntegersBar {F : IntermediateField ℚ (LaurentSeries ℚ)} [i : Algebra ℚ F] (h : ∃ j : F, (qSeriesBar ℚ F j).order = -1) (v : Place ℚ F) (hv : v.toValuationSubring = qIntegersBar ℚ F) : v.deg = 1 := by sorry
