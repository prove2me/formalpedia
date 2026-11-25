-- Prove2me | Theorems.Thm_GlobalTheory_ToricData_map_top_inj
-- name    : GlobalTheory.ToricData.map_top_inj
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T14:32:29.034305+00:00
-- url     : https://prove2.me/theorems/c4005b45-bbbd-49ef-a4ce-7e93d7c4d458
-- title:
--   Toric Data: map top inj
-- statement:
--   The Toric Data construction uses the map top inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/PullTopZFConstUnit.lean#L27-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/PullTopZFConstUnit.lean#L27-L31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_PsiWeightZeroLinearCombination
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_PullTopZFConstUnit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.Inh ReciprocityTheory.ChartRestriction.G.Out.InhTate ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ToricData
variable {Z Y : Scheme.{0}} {J J₁ J₂ J₃ : Type} [Fintype J] [Fintype J₁] [Fintype J₂] [Fintype J₃]

theorem GlobalTheory.ToricData.map_top_inj {V : Y.Opens} (hV : V = ⊤) {a b : Γ(Y, ⊤)}
    (h : (Y.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom a = (Y.presheaf.map (homOfLE le_top).op).hom b) :
    a = b := by sorry
