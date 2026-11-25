-- Prove2me | Theorems.Thm_GroundTheory_Arith_Etale_pullbackUnitApp_bijective
-- name    : GroundTheory.Arith.Etale.pullbackUnitApp_bijective
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:04:58.649163+00:00
-- url     : https://prove2.me/theorems/064f8909-924a-4c70-9b48-5c28827ce519
-- title:
--   Etale: pullback Unit App bijective
-- statement:
--   The Etale construction uses the pullback Unit App bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/EtaleCompletion/QcohZariski.lean#L51-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/EtaleCompletion/QcohZariski.lean#L51-L74

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
variable {V T U : Scheme.{u}}

theorem GroundTheory.Arith.Etale.pullbackUnitApp_bijective (j : T ⟶ U) [IsOpenImmersion j] (N : U.Modules) {O : U.Opens}
    (hO : O ≤ j.opensRange) : Function.Bijective (pullbackUnitApp j N O) := by sorry
