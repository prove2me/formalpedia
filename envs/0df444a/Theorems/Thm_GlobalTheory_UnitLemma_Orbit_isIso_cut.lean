-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_Orbit_isIso_cut
-- name    : GlobalTheory.UnitLemma.Orbit.isIso_cut
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:42:26.6976+00:00
-- url     : https://prove2.me/theorems/99cf5b40-6e93-5a04-b3e6-40d73faa8662
-- title:
--   Orbit: is Iso cut
-- statement:
--   The Orbit construction uses the is Iso cut property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLocalRingOfIdem.lean#L390-L393
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLocalRingOfIdem.lean#L390-L393

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EqZeroOfNotPrimary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Orbit
open GlobalTheory.UnitLemma Polynomial IsLocalRing ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion
variable {K : UQ}

theorem GlobalTheory.UnitLemma.Orbit.isIso_cut (B : InvAlg K) {e : B.A} (hi : IsIdempotentElem e) (he : B.σ e = e) :
    IsIso (B := B) (C := (cut B e he).prod (cut B (1 - e) (one_sub_fixed B he)))
      (AlgEquiv.prodQuotientOfIsIdempotentElem K.E hi hi.one_sub (by simp) (by simp [hi])) := by sorry
