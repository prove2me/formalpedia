-- Prove2me | Theorems.Thm_GlobalTheory_TrivLocus_nonempty_of_ne_zero
-- name    : GlobalTheory.TrivLocus.nonempty_of_ne_zero
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T11:27:38.589387+00:00
-- url     : https://prove2.me/theorems/306c1457-ba10-4708-97a1-5427a4a624b0
-- title:
--   Triv Locus: nonempty of ne zero
-- statement:
--   The Triv Locus construction uses the nonempty of ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsKerIffMinors.lean#L90-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsKerIffMinors.lean#L90-L94

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

theorem GlobalTheory.TrivLocus.nonempty_of_ne_zero {U : X.Opens} {x : Γ(X, U)} (hx : x ≠ 0) : (U : Set X).Nonempty := by sorry
