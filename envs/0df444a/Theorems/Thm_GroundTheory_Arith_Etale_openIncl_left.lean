-- Prove2me | Theorems.Thm_GroundTheory_Arith_Etale_openIncl_left
-- name    : GroundTheory.Arith.Etale.openIncl_left
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:05:55.998071+00:00
-- url     : https://prove2.me/theorems/e15d33d5-72bb-45da-a969-961875cf2a37
-- title:
--   Etale: open Incl left
-- statement:
--   The Etale construction uses the open Incl left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/EtaleCompletion/QcohZariski.lean#L98-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/EtaleCompletion/QcohZariski.lean#L98-L98

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_EtaleCompletion_QcohPresheaf
import Definitions.Def_GroundTheory_ArithmeticGeometry_EtaleCompletion_QcohZariski
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Etale
open CategoryTheory Limits Opposite AlgebraicGeometry
universe u
variable {X : Scheme.{u}} (F : X.Modules) (U : X.Etale)

theorem GroundTheory.Arith.Etale.openIncl_left (O : U.left.Opens) : (openIncl U O).left = O.ι := by sorry

attribute [defeq] GroundTheory.Arith.Etale.openIncl_left
