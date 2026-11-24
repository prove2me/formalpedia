-- Prove2me | Theorems.Thm_GlobalTheory_DualLabel_rootsBar_normRev
-- name    : GlobalTheory.DualLabel.rootsBar_normRev
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:01:11.8053+00:00
-- url     : https://prove2.me/theorems/1d4b5ff3-5641-46f1-84da-32857bb15b78
-- title:
--   Dual Label: roots Bar norm Rev
-- statement:
--   The Dual Label construction uses the roots Bar norm Rev property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RootsReverseProd.lean#L34-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RootsReverseProd.lean#L34-L45

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_CoeffZeroNeOfMonicIrr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RootsReverseProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial CategoryTheory
open GlobalTheory GlobalTheory.DualLabel

theorem GlobalTheory.DualLabel.rootsBar_normRev {K : Type} [Field K] {f : K[X]} (hm : f.Monic) (h0 : f.coeff 0 ≠ 0) :
    Formalism.IrreducibleCountingLemmas.TYPES.rootsBar K (C (f.coeff 0)⁻¹ * f.reverse) =
      (Formalism.IrreducibleCountingLemmas.TYPES.rootsBar K f).map (·⁻¹) := by sorry
