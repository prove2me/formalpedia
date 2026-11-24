-- Prove2me | Theorems.Thm_GlobalTheory_DualLabel_roots_reverse_prod
-- name    : GlobalTheory.DualLabel.roots_reverse_prod
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:01:55.257482+00:00
-- url     : https://prove2.me/theorems/d0a4f3b6-cce0-4ed1-b4a6-4cd38ca5dbf5
-- title:
--   Dual Label: roots reverse prod
-- statement:
--   The Dual Label construction uses the roots reverse prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RootsReverseProd.lean#L10-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RootsReverseProd.lean#L10-L27

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

theorem GlobalTheory.DualLabel.roots_reverse_prod {K : Type} [Field K] (s : Multiset K) (hs : (0 : K) ∉ s) :
    ((s.map fun x => X - C x).prod.reverse).roots = s.map (·⁻¹) := by sorry
