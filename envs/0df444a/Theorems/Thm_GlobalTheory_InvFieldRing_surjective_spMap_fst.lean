-- Prove2me | Theorems.Thm_GlobalTheory_InvFieldRing_surjective_spMap_fst
-- name    : GlobalTheory.InvFieldRing.surjective_spMap_fst
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:12:04.883689+00:00
-- url     : https://prove2.me/theorems/c7687f1a-c5d8-538f-a54c-c64c9539702a
-- title:
--   Inv Field Ring: surjective sp Map fst
-- statement:
--   The Inv Field Ring construction uses the surjective sp Map fst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SurjectiveSpMapFst.lean#L64-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SurjectiveSpMapFst.lean#L64-L74

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__DenseInterior_23def473f6482931
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DualNumberSectionsUniqueDecomposition
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SurjectiveSpMapFst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
open MonoidalCategory CartesianMonoidalCategory MonObj
noncomputable section
open GlobalTheory GlobalTheory.InvFieldRing
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.InvFieldRing.surjective_spMap_fst (R : Type) [CommRing R] : Surjective (spMap (TrivSqZeroExt.fstHom R R R).toRingHom) := by sorry
