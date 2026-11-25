-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_Orbit_isLocalRing_of_idem
-- name    : GlobalTheory.UnitLemma.Orbit.isLocalRing_of_idem
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:42:30.394948+00:00
-- url     : https://prove2.me/theorems/0ea96a75-7c26-42bd-8815-81f83621e1d7
-- title:
--   Orbit: is Local Ring of idem
-- statement:
--   The Orbit construction uses the is Local Ring of idem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLocalRingOfIdem.lean#L12-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLocalRingOfIdem.lean#L12-L67

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

theorem GlobalTheory.UnitLemma.Orbit.isLocalRing_of_idem {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R] (S : Type*) [CommRing S] [Nontrivial S] [Algebra R S]
    [Module.Finite R S] (hid : ∀ e : S, e * e = e → e = 0 ∨ e = 1) : IsLocalRing S := by sorry
