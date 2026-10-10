-- Prove2me | Theorems.Thm_MazurTransfer_order13_actual_section_exists_over_every_field
-- name    : MazurTransfer.order13_actual_section_exists_over_every_field
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-09T17:05:27.865597+00:00
-- url     : https://prove2.me/theorems/0e06331a-b531-472f-bd1a-30d8cbab6028
-- title:
--   Actual order-13 two-chart curve has an explicit section over every field
-- statement:
--   Let $K$ be any field and let $C_K$ be the literal two-chart curve formed from
--   $$y^2=x^6+2x^5+x^4+2x^3+6x^2+4x+1$$
--   and its reciprocal chart, with structural morphism $\pi_K:C_K\to\operatorname{Spec}(K)$. Then
--   $$\exists\,s_K:\operatorname{Spec}(K)\to C_K,\qquad \pi_K\circ s_K=\operatorname{id}_{\operatorname{Spec}(K)}.$$
--   The section comes from the ordinary-chart point $(0,1)$. This theorem supplies the base point for actual Picard rigidification. It holds in every characteristic; smoothness, Picard representation and the Jacobian comparison remain separate obligations.
-- source:
--   Vas and contributors, MazurTheorem at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c, Apache-2.0: https://github.com/Vilin97/MazurTheorem/tree/54d43d8dda8a6fcf069cc02a815f850d762c5c0c/MazurTorsion . Literal coordinate-ring evaluation and ordinary chart give the section (0,1), with structural equation proved by Spec functoriality and the algebra-map unit law. The previously checked characteristic-zero construction is shown to require only a field; no curve model, smoothness or Picard representation is assumed.

import Mathlib
import Definitions.Def_MazurTransfer_Order13ExplicitCurve
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
open AlgebraicGeometry CategoryTheory NeronModelInfra

theorem MazurTransfer.order13_actual_section_exists_over_every_field.{u} (K : Type u) [Field K] :
    Nonempty (SchemeHomOver (𝟙 (Spec (CommRingCat.of K)))
      (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K)) := by sorry
