-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_isGalois_untiltField
-- name    : GroundTheory.PAdicHodge.isGalois_untiltField
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:07:54.963768+00:00
-- url     : https://prove2.me/theorems/9aa3705c-83d6-5b85-97c5-e833fdfa306c
-- title:
--   PAdic Hodge: is Galois untilt Field
-- statement:
--   The PAdic Hodge construction uses the is Galois untilt Field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UntiltGaloisCorr.lean#L99-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UntiltGaloisCorr.lean#L99-L101

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

theorem GroundTheory.PAdicHodge.isGalois_untiltField (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N]
    [IsGalois K♭ N] : IsGalois K (untiltField K C p N) := by sorry
