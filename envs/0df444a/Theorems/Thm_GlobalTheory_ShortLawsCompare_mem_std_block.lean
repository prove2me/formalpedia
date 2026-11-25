-- Prove2me | Theorems.Thm_GlobalTheory_ShortLawsCompare_mem_std_block
-- name    : GlobalTheory.ShortLawsCompare.mem_std_block
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:31:12.83947+00:00
-- url     : https://prove2.me/theorems/c76b59c8-4734-40ee-9a15-8cf27b2a0dc0
-- title:
--   Short Laws Compare: mem std block
-- statement:
--   The Short Laws Compare construction uses the mem std block property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/BlockHarmLevOfBlockHarm.lean#L31-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/BlockHarmLevOfBlockHarm.lean#L31-L42

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_BlockPolyLevelMove
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_BlockProductLattices
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIndexIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_BetaIsPrincipal
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_ZeroNotAdmissibleOfRankPos
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_BaseClassMove
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_BlockHarmLevOfBlockHarm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ShortLawsCompare
open NumberField MvPolynomial Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.IndefiniteRowSideFullHecke
variable {E : Type} [Field E] [NumberField E]
variable {n₁ n₂ : ℕ}
set_option autoImplicit false
open NumberField MvPolynomial
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
variable {E : Type} [Field E] [NumberField E]
variable {n₁ n₂ : ℕ}

theorem GlobalTheory.ShortLawsCompare.mem_std_block (v : Fin (n₁ + n₂) → E) :
    v ∈ _root_.Formalism.L2.Pj.stdLat E (n₁ + n₂) ↔
      (fun j => v (Fin.castAdd n₂ j)) ∈ _root_.Formalism.L2.Pj.stdLat E n₁ ∧
        (fun j => v (Fin.natAdd n₁ j)) ∈ _root_.Formalism.L2.Pj.stdLat E n₂ := by sorry
