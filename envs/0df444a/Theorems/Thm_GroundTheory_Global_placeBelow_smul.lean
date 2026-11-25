-- Prove2me | Theorems.Thm_GroundTheory_Global_placeBelow_smul
-- name    : GroundTheory.Global.placeBelow_smul
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:14:46.964139+00:00
-- url     : https://prove2.me/theorems/c3f23740-843a-521b-979d-6c738fcf6ccc
-- title:
--   Global: place Below smul
-- statement:
--   The Global construction uses the place Below smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/SUnitsPerm.lean#L100-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/SUnitsPerm.lean#L100-L105

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Permutation
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_LatticeBridge
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Galois
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_SUnitsPerm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open MulAction NumberField IsDedekindDomain
open scoped Pointwise
noncomputable section
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]
omit [NumberField K] [NumberField L] [IsGalois K L]

theorem GroundTheory.Global.placeBelow_smul (g : L ≃ₐ[K] L) (w : HeightOneSpectrum (𝓞 L)) :
    placeBelow (K := K) (g • w) = placeBelow w := by sorry
