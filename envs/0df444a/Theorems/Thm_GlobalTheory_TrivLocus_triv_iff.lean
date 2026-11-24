-- Prove2me | Theorems.Thm_GlobalTheory_TrivLocus_triv_iff
-- name    : GlobalTheory.TrivLocus.triv_iff
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T11:27:36.689722+00:00
-- url     : https://prove2.me/theorems/c01cd5bb-f902-42d1-868c-43c69c752861
-- title:
--   Triv Locus: triv iff
-- statement:
--   The Triv Locus construction uses the triv iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsKerIffMinors.lean#L96-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsKerIffMinors.lean#L96-L147

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsKerIffMinors
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
noncomputable section
open GlobalTheory GlobalTheory.TrivLocus
variable {X Y : Scheme.{0}}

theorem GlobalTheory.TrivLocus.triv_iff [IsIntegral X] (hX : IsField Γ(X, ⊤)) (N : LB X) (hN : ⨆ i, N.U i = ⊤) :
    Triv N ↔ Nontrivial (LB.Sec N) ∧ Nontrivial (LB.Sec (pw N (-1))) := by sorry
