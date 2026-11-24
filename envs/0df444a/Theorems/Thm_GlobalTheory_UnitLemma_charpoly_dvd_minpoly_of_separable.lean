-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_charpoly_dvd_minpoly_of_separable
-- name    : GlobalTheory.UnitLemma.charpoly_dvd_minpoly_of_separable
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:38:00.827683+00:00
-- url     : https://prove2.me/theorems/d32535fd-4c37-4416-8e90-286ae4fee81d
-- title:
--   Unit Lemma: charpoly dvd minpoly of separable
-- statement:
--   The Unit Lemma construction uses the charpoly dvd minpoly of separable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsPowerBasisOfCharpolySeparable.lean#L15-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsPowerBasisOfCharpolySeparable.lean#L15-L42

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsPowerBasisOfCharpolySeparable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Matrix MeasureTheory
open GlobalTheory GlobalTheory.UnitLemma
open Polynomial
open Matrix MeasureTheory
open Polynomial

theorem GlobalTheory.UnitLemma.charpoly_dvd_minpoly_of_separable {E V : Type} [Field E] [AddCommGroup V] [Module E V]
    [Module.Finite E V] (f : Module.End E V) (h : (LinearMap.charpoly f).Separable) :
    LinearMap.charpoly f ∣ minpoly E f := by sorry
