-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_Orbit_eta_gram
-- name    : GlobalTheory.UnitLemma.Orbit.eta_gram
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T20:59:59.239861+00:00
-- url     : https://prove2.me/theorems/ca4d60c2-976c-489d-957f-7cf76aee3b2e
-- title:
--   Orbit: eta gram
-- statement:
--   The Orbit construction uses the eta gram property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLocalRingOfIdem.lean#L186-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLocalRingOfIdem.lean#L186-L205

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

theorem GlobalTheory.UnitLemma.Orbit.eta_gram (B : InvAlg K) (x : B.A) (b : Module.Basis (Fin (Module.finrank K.E B.A)) K.E B.A) :
    K.eta (Matrix.of fun i j => B.herm x (b i) (b j)).det = K.eta (B.gramDet x) := by sorry
