-- Prove2me | Theorems.Thm_GlobalTheory_LevelUnimod_levDiag_inv
-- name    : GlobalTheory.LevelUnimod.levDiag_inv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:16:21.978678+00:00
-- url     : https://prove2.me/theorems/62063e2c-ad78-4e76-b3ce-972f49b48f20
-- title:
--   Level Unimod: lev Diag inv
-- statement:
--   The Level Unimod construction uses the lev Diag inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsUnimodularBlockUpperTriangularSymmetricLevels.lean#L106-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsUnimodularBlockUpperTriangularSymmetricLevels.lean#L106-L107

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FourierJacobiAverage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsMulLeftInvariantVolGL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_GlCharacterEqOneOfTransposeInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsUnimodularBlockUpperTriangularSymmetricLevels
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
open scoped Topology
open GlobalTheory GlobalTheory.LevelUnimod
variable {k : Type} [Field k] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem GlobalTheory.LevelUnimod.levDiag_inv (lev : ι → ℕ) (t : kˣ) : (levDiag lev t)⁻¹ = levDiag lev t⁻¹ := by sorry
