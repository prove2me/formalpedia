-- Prove2me | Theorems.Thm_GlobalTheory_PolyNorm_det_eq_prod
-- name    : GlobalTheory.PolyNorm.det_eq_prod
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T18:50:37.144478+00:00
-- url     : https://prove2.me/theorems/a100e4b1-3cfc-4d30-85fd-43dbe04daf11
-- title:
--   Poly Norm: det eq prod
-- statement:
--   The Poly Norm construction uses the det eq prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/EqProdOfMul.lean#L236-L246
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/EqProdOfMul.lean#L236-L246

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EqOfNormResultantEqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EqProdOfMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.PolyNorm

theorem GlobalTheory.PolyNorm.det_eq_prod {K : Type} [Field K] [IsAlgClosed K] {m : ℕ} (V : Matrix (Fin m) (Fin m) K)
    (b : Multiset K) (hb : V.charpoly = (b.map fun x => X - C x).prod) (F : K[X]) :
    (aeval V F).det = (b.map fun x => F.eval x).prod := by sorry
