-- Prove2me | Theorems.Thm_GlobalTheory_LatClass_lat_of_coset
-- name    : GlobalTheory.LatClass.lat_of_coset
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:10:08.962078+00:00
-- url     : https://prove2.me/theorems/2c777fdb-e336-4388-b2cf-4a0ad8aad765
-- title:
--   Lat Class: lat of coset
-- statement:
--   The Lat Class construction uses the lat of coset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LatticeClasses.lean#L15-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LatticeClasses.lean#L15-L20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_NormalRepresentationLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LatticeBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsValuationEqZpow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MulMemOfHatCosetIndNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FlatNeZeroOfMemR
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_TwistSupportPeriodicLevels
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LatticeClasses
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice
open GlobalTheory GlobalTheory.LatClass
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.LatClass.lat_of_coset {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} {J : Subgroup (GL (n ⊕ Fin c) k)}
    (hJ : J ≤ KO k _) {a b : GL (n ⊕ Fin c) k}
    (h : DoubleCoset.mk (R k n c 1) J a = DoubleCoset.mk (R k n c 1) J b) :
    ∃ r ∈ R k n c 1, latOf b = latOf (r * a) := by sorry
