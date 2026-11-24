-- Prove2me | Theorems.Thm_GlobalTheory_LocalFiniteOddFixed_isLocalRing_of_finite
-- name    : GlobalTheory.LocalFiniteOddFixed.isLocalRing_of_finite
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T18:14:13.895322+00:00
-- url     : https://prove2.me/theorems/c0562c41-0947-4207-8ae0-d5e72f283c16
-- title:
--   Local Finite Odd Fixed: is Local Ring of finite
-- statement:
--   The Local Finite Odd Fixed construction uses the is Local Ring of finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLocalRingOfFinite.lean#L50-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLocalRingOfFinite.lean#L50-L97

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.LocalFiniteOddFixed

theorem GlobalTheory.LocalFiniteOddFixed.isLocalRing_of_finite (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]
    (R : Type) [CommRing R] [IsDomain R] [Algebra O R] [Module.Finite O R] : IsLocalRing R := by sorry
