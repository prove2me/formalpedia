-- Prove2me | Theorems.Thm_GlobalTheory_IntegralFrameAllCompare_extension_iff
-- name    : GlobalTheory.IntegralFrameAllCompare.extension_iff
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T01:05:11.262743+00:00
-- url     : https://prove2.me/theorems/7fcfc515-8570-471b-bc93-3e3ec341fbc0
-- title:
--   Integral Frame All Compare: extension iff
-- statement:
--   The Integral Frame All Compare construction uses the extension iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/VVNonnegIffLeOne.lean#L140-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/VVNonnegIffLeOne.lean#L140-L154

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntAllFree
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_IntegralFrameAcquisition
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_VVNonnegIffLeOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open GlobalTheory GlobalTheory.IntegralFrameAllCompare
open NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.IntegralFrameAcquisition

theorem GlobalTheory.IntegralFrameAllCompare.extension_iff {F : Type} [Field F] [NumberField F] {la : HeightOneSpectrum (𝓞 F)} {T T' : CDVR}
    {io : F →+* T.Fr} {e : ℕ} (ho : OverLa la T.V io e) (hT' : T'.FinRes) (j : T.Fr →+* T'.Fr) (e' : ℕ) :
    (OverLa la T'.V (j.comp io) e' ∧
        ∀ a : T.V, j (algebraMap T.V T.Fr a) ∈ Set.range (algebraMap T'.V T'.Fr)) ↔
      ∃ r : ℕ, e' = r * e ∧ IsFiniteValuedExt T T' j r ∧ OverLa la T'.V (j.comp io) (r * e) := by sorry
