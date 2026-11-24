-- Prove2me | Theorems.Thm_FunctorialResolution_Blowup_idealSheafData_prod_cons
-- name    : FunctorialResolution.Blowup.idealSheafData_prod_cons
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:14:52.802458+00:00
-- url     : https://prove2.me/theorems/78122a3d-c254-4115-ae0b-597d69ead049
-- title:
--   Blowup: ideal Sheaf Data prod cons
-- statement:
--   The Blowup construction uses the ideal Sheaf Data prod cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Schemes/IdealSheafData.lean#L453-L455
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Schemes/IdealSheafData.lean#L453-L455

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_AffineOpens
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry Opposite
open FunctorialResolution FunctorialResolution.Blowup

theorem FunctorialResolution.Blowup.idealSheafData_prod_cons (X : Scheme.{u}) (D : X.IdealSheafData)
    (E : List X.IdealSheafData) : (D :: E).prod = D * E.prod := by sorry
