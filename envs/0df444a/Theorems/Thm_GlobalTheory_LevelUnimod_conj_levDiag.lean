-- Prove2me | Theorems.Thm_GlobalTheory_LevelUnimod_conj_levDiag
-- name    : GlobalTheory.LevelUnimod.conj_levDiag
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:16:17.940565+00:00
-- url     : https://prove2.me/theorems/9ab46813-3d44-4082-8aef-885c41e93561
-- title:
--   Level Unimod: conj lev Diag
-- statement:
--   The Level Unimod construction uses the conj lev Diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsUnimodularBlockUpperTriangularSymmetricLevels.lean#L109-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsUnimodularBlockUpperTriangularSymmetricLevels.lean#L109-L113

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

theorem GlobalTheory.LevelUnimod.conj_levDiag (lev : ι → ℕ) (t : kˣ) (g : GL ι k) (r s : ι) :
    ((levDiag lev t)⁻¹ * g * levDiag lev t).val r s =
      ((t⁻¹ : kˣ) : k) ^ lev r * g.val r s * (t : k) ^ lev s := by sorry
