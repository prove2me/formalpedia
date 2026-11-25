-- Prove2me | Theorems.Thm_GlobalTheory_ShortLawsCompare_unimod_std
-- name    : GlobalTheory.ShortLawsCompare.unimod_std
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:26:19.928548+00:00
-- url     : https://prove2.me/theorems/0de80670-66f2-45bc-89da-9cb97f8f5553
-- title:
--   Short Laws Compare: unimod std
-- statement:
--   The Short Laws Compare construction uses the unimod std property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/BlockHarmLevOfBlockHarm.lean#L117-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/BlockHarmLevOfBlockHarm.lean#L117-L150

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

theorem GlobalTheory.ShortLawsCompare.unimod_std [IsCMField E] (n : ℕ) :
    _root_.Formalism.L2.Pj.GenLat.Unimod (⟨_root_.Formalism.L2.Pj.stdLat E n⟩ : _root_.Formalism.L2.Pj.GenLat E n) := by sorry
