-- Prove2me | Theorems.Thm_GlobalTheory_LipschitzCovol_embPlace_symm_apply
-- name    : GlobalTheory.LipschitzCovol.embPlace_symm_apply
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T18:11:42.809499+00:00
-- url     : https://prove2.me/theorems/cfad34c0-7cf0-4f9a-a116-f73da4af518d
-- title:
--   Lipschitz Covol: emb Place symm apply
-- statement:
--   The Lipschitz Covol construction uses the emb Place symm apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CovolumeFractionalIdealRealLatticeImage.lean#L32-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CovolumeFractionalIdealRealLatticeImage.lean#L32-L33

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RembApply
import Definitions.Def_Formalism_LatticeTheta_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CovolumeFractionalIdealRealLatticeImage
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField nonZeroDivisors MeasureTheory GlobalTheory.LipschitzTR GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
open scoped FourierTransform RealInnerProductSpace
noncomputable section
open GlobalTheory GlobalTheory.LipschitzCovol
open NumberField.InfinitePlace NumberField.mixedEmbedding
open scoped Classical
variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem GlobalTheory.LipschitzCovol.embPlace_symm_apply (w : {w : InfinitePlace F // IsReal w}) :
    (embPlace.symm w : F →+* ℝ) = embedding_of_isReal w.2 := by sorry
