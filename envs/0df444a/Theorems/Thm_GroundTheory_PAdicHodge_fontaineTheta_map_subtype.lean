-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_fontaineTheta_map_subtype
-- name    : GroundTheory.PAdicHodge.fontaineTheta_map_subtype
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:17:56.688843+00:00
-- url     : https://prove2.me/theorems/43721ea8-9d2f-4b74-8ef7-5437428544a4
-- title:
--   PAdic Hodge: fontaine Theta map subtype
-- statement:
--   The PAdic Hodge construction uses the fontaine Theta map subtype property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UntiltGaloisCorr.lean#L112-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UntiltGaloisCorr.lean#L112-L124

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

theorem GroundTheory.PAdicHodge.fontaineTheta_map_subtype (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N]
    (u : WittVector p (integerTilt K C p N)) :
    ((WittVector.fontaineTheta (normInteger C) p (WittVector.map (integerTilt K C p N).subtype u) :
        normInteger C) : C) =
      ((WittVector.fontaineTheta (normInteger (untiltField K C p N)) p
          (WittVector.map (preTiltUntiltEquiv N).symm.toRingHom u) :
        normInteger (untiltField K C p N)) : untiltField K C p N) := by sorry
