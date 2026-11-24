-- Prove2me | Theorems.Thm_GroundTheory_Global_SUnit_finrank_quotient_torsion
-- name    : GroundTheory.Global.SUnit.finrank_quotient_torsion
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:40:20.654876+00:00
-- url     : https://prove2.me/theorems/bfd4a9f4-48f3-4756-9d16-ebc219ff8e12
-- title:
--   SUnit: finrank quotient torsion
-- statement:
--   The SUnit construction uses the finrank quotient torsion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ExistenceTheorem/PowerIndex.lean#L87-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ExistenceTheorem/PowerIndex.lean#L87-L90

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SUnits
import Definitions.Def_GroundTheory_GlobalFields_ExistenceTheorem_PowerIndex
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
open NumberField IsDedekindDomain Module
noncomputable section
variable {K : Type*} [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K)))
open GroundTheory.Global.SUnit

theorem GroundTheory.Global.SUnit.finrank_quotient_torsion [Finite S] :
    finrank ℤ (Additive (S.unit K ⧸ CommGroup.torsion (S.unit K))) = Units.rank K + Nat.card S := by sorry
