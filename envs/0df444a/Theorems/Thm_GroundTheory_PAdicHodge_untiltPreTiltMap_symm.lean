-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_untiltPreTiltMap_symm
-- name    : GroundTheory.PAdicHodge.untiltPreTiltMap_symm
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:17:27.892144+00:00
-- url     : https://prove2.me/theorems/fca246b3-1a70-5acf-be0a-77a1841a38e9
-- title:
--   PAdic Hodge: untilt Pre Tilt Map symm
-- statement:
--   The PAdic Hodge construction uses the untilt Pre Tilt Map symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UntiltGaloisCorr.lean#L107-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UntiltGaloisCorr.lean#L107-L110

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_UntiltGalois
import Definitions.Def_GroundTheory_PAdicHodge_UntiltGaloisCorr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
variable {K C : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [NontriviallyNormedField C] [IsUltrametricDist C] [NormedAlgebra K C]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p] [IsPerfectoidField C p]
local notation "K♭" => Tilt K NormedField.valuation (normInteger K) normInteger_integers p
local notation "C♭" => Tilt C NormedField.valuation (normInteger C) normInteger_integers p
local notation "𝒪K♭" => PreTilt (normInteger K) p
local notation "𝒪C♭" => PreTilt (normInteger C) p

theorem GroundTheory.PAdicHodge.untiltPreTiltMap_symm (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N]
    (a : integerTilt K C p N) :
    untiltPreTiltMap N ((preTiltUntiltEquiv N).symm a) = a := by sorry
