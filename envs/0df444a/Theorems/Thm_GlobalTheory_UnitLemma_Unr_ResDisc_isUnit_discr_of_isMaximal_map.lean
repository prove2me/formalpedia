-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_Unr_ResDisc_isUnit_discr_of_isMaximal_map
-- name    : GlobalTheory.UnitLemma.Unr.ResDisc.isUnit_discr_of_isMaximal_map
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T21:35:37.069039+00:00
-- url     : https://prove2.me/theorems/164c85fd-8d76-4e69-8658-1231a3044c41
-- title:
--   Res Disc: is Unit discr of is Maximal map
-- statement:
--   The Res Disc construction uses the is Unit discr of is Maximal map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsUnitTraceFormDiscrUnramifiedExt.lean#L12-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsUnitTraceFormDiscrUnramifiedExt.lean#L12-L35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsUnitTraceFormDiscrUnramifiedExt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr GlobalTheory.UnitLemma.Unr.ResDisc
open IsLocalRing

theorem GlobalTheory.UnitLemma.Unr.ResDisc.isUnit_discr_of_isMaximal_map {R S : Type} [CommRing R] [IsLocalRing R] [CommRing S] [Algebra R S]
    [Finite (ResidueField R)] {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R S)
    (hmax : (Ideal.map (algebraMap R S) (maximalIdeal R)).IsMaximal) :
    IsUnit (Algebra.discr R b) := by sorry
