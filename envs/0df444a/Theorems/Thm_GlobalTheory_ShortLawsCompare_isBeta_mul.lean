-- Prove2me | Theorems.Thm_GlobalTheory_ShortLawsCompare_isBeta_mul
-- name    : GlobalTheory.ShortLawsCompare.isBeta_mul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:26:21.851108+00:00
-- url     : https://prove2.me/theorems/146a77f4-5c34-4ca9-9297-7186f4ea07c7
-- title:
--   Short Laws Compare: is Beta mul
-- statement:
--   The Short Laws Compare construction uses the is Beta mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/BlockHarmLevOfBlockHarm.lean#L268-L293
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/BlockHarmLevOfBlockHarm.lean#L268-L293

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
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (c : Coeff l)
set_option autoImplicit false
open NumberField MvPolynomial
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H}
  {l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
variable (c : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l)

theorem GlobalTheory.ShortLawsCompare.isBeta_mul {n : ℕ} {Λ : _root_.Formalism.L2.Pj.GenLat E n} {β ζ : c.F}
    (h : _root_.GlobalTheory.IndefiniteRowSideFullHecke.BlockLatticeAdmissibility.IsBeta Dw c Λ β) (hζ : IsOfFinOrder ζ) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.BlockLatticeAdmissibility.IsBeta Dw c Λ (ζ * β) := by sorry
