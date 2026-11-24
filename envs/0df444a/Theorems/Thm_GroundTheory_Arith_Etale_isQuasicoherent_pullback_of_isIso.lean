-- Prove2me | Theorems.Thm_GroundTheory_Arith_Etale_isQuasicoherent_pullback_of_isIso
-- name    : GroundTheory.Arith.Etale.isQuasicoherent_pullback_of_isIso
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:33:06.49313+00:00
-- url     : https://prove2.me/theorems/571f930f-3772-42c5-8534-6dab0432c35b
-- title:
--   Etale: is Quasicoherent pullback of is Iso
-- statement:
--   The Etale construction uses the is Quasicoherent pullback of is Iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/EtaleCompletion/PullbackAffine.lean#L209-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/EtaleCompletion/PullbackAffine.lean#L209-L212

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_EtaleCompletion_ModulesPullback
import Definitions.Def_GroundTheory_ArithmeticGeometry_EtaleCompletion_PullbackAffine
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

theorem GroundTheory.Arith.Etale.isQuasicoherent_pullback_of_isIso {T U : Scheme.{u}} (g : T ⟶ U) [IsIso g] (N : U.Modules)
    [N.IsQuasicoherent] : ((Scheme.Modules.pullback g).obj N).IsQuasicoherent := by sorry
