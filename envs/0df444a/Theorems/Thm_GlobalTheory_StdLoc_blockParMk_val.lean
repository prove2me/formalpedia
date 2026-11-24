-- Prove2me | Theorems.Thm_GlobalTheory_StdLoc_blockParMk_val
-- name    : GlobalTheory.StdLoc.blockParMk_val
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:38:10.483868+00:00
-- url     : https://prove2.me/theorems/67167a96-7bf4-4a8d-9dbc-1984ead224cf
-- title:
--   Std Loc: block Par Mk val
-- statement:
--   The Std Loc construction uses the block Par Mk val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CardBlockParabolicSubgroupGL.lean#L34-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CardBlockParabolicSubgroupGL.lean#L34-L36

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RowBlockIndicatorFromLtIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardBlockParabolicSubgroupGL
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField UniqueFactorizationMonoid GlobalTheory.StdLoc
noncomputable section
open GlobalTheory GlobalTheory.StdLoc

theorem GlobalTheory.StdLoc.blockParMk_val {R : Type} [CommRing R] {a b : ℕ}
    (x : GL (Fin a) R × GL (Fin b) R × Matrix (Fin a) (Fin b) R) :
    ((blockParMk x).1 : Matrix (Fin (a + b)) (Fin (a + b)) R) = blockMat x.1.1 x.2.2 x.2.1.1 := by sorry
