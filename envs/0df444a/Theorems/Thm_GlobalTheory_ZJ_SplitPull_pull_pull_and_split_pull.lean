-- Prove2me | Theorems.Thm_GlobalTheory_ZJ_SplitPull_pull_pull_and_split_pull
-- name    : GlobalTheory.ZJ.SplitPull.pull_pull_and_split_pull
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T17:02:37.074442+00:00
-- url     : https://prove2.me/theorems/889f2f4a-082a-5c1f-a115-04c73ddf4663
-- title:
--   Split Pull: pull pull and split pull
-- statement:
--   The Split Pull construction uses the pull pull and split pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/PullPullAndSplitPull.lean#L178-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/PullPullAndSplitPull.lean#L178-L205

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsNormalSchemeSp
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsAffineSplitTorusLeft
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_PullPullAndSplitPull
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
noncomputable section
open GlobalTheory GlobalTheory.ZJ GlobalTheory.ZJ.SplitPull
open GlobalTheory.UU

theorem GlobalTheory.ZJ.SplitPull.pull_pull_and_split_pull : (∀ (X Y Y' : Scheme.{0}) (C : Charts X) (φ : Y ⟶ X) (ψ : Y' ⟶ Y) [IsAffineHom φ] [IsAffineHom ψ], (C.pull φ).pull ψ = C.pull (ψ ≫ φ)) ∧ ∀ (K K' : Type) [Field K] [Field K'] (H : Over (Sp K)) [GrpObj H] (H' : Over (Sp K')) [GrpObj H'] (f : Sp K' ⟶ Sp K) (φ : H'.left ⟶ H.left) [IsAffineHom φ], IsGrpPullback H' H f φ → ∀ (C : Charts H.left) (d : ℕ) (c : Fin d → C.Cl), C.Split c → Charts.Split (C.pull φ) c := by sorry
