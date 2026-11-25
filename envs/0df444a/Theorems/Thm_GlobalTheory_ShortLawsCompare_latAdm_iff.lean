-- Prove2me | Theorems.Thm_GlobalTheory_ShortLawsCompare_latAdm_iff
-- name    : GlobalTheory.ShortLawsCompare.latAdm_iff
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:24:00.583855+00:00
-- url     : https://prove2.me/theorems/deedc55d-06b5-4c32-afc2-e88de9bd9b8f
-- title:
--   Short Laws Compare: lat Adm iff
-- statement:
--   The Short Laws Compare construction uses the lat Adm iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/BlockHarmLevOfBlockHarm.lean#L318-L318
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/BlockHarmLevOfBlockHarm.lean#L318-L318

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
variable (c : Coeff l) {n₁ n₂ : ℕ}

theorem GlobalTheory.ShortLawsCompare.latAdm_iff {n : ℕ} (bad : ℕ) (Λ : GenLat E n) : BlockLatticeAdmissibility.LatAdm l bad Λ ↔ BlockProductLattices.LatOK bad l.M Λ := by sorry
