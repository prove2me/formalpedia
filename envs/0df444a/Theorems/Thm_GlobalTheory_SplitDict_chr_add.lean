-- Prove2me | Theorems.Thm_GlobalTheory_SplitDict_chr_add
-- name    : GlobalTheory.SplitDict.chr_add
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T20:20:46.837805+00:00
-- url     : https://prove2.me/theorems/e2521594-a057-4e03-914d-969d0c1694ac
-- title:
--   Split Dict: chr add
-- statement:
--   The Split Dict construction uses the chr add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsBoxInvariantSnd.lean#L290-L291
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsBoxInvariantSnd.lean#L290-L291

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_GL2CharacterZeros
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierTransformInversionLocalFieldPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsBoxInvariantSnd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi GlobalTheory.IndefiniteRowSideFullHecke.GLMatrixJoining
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.SplitDict
variable {k : Type} [Field k]

theorem GlobalTheory.SplitDict.chr_add (ψ : AddChar k Circle) (s : ℤˣ) (x y : k) : chr ψ s (x + y) = chr ψ s x * chr ψ s y := by sorry
