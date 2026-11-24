-- Prove2me | Theorems.Thm_GlobalTheory_PolyNorm_natDegree_gen
-- name    : GlobalTheory.PolyNorm.natDegree_gen
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T18:50:29.348848+00:00
-- url     : https://prove2.me/theorems/3daadce8-9b59-4fcf-8504-9ad81e2b3ac6
-- title:
--   Poly Norm: nat Degree gen
-- statement:
--   The Poly Norm construction uses the nat Degree gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/EqProdOfMul.lean#L32-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/EqProdOfMul.lean#L32-L36

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

theorem GlobalTheory.PolyNorm.natDegree_gen {r : ℕ} {K : Type} [CommRing K] (f : Fin (r + 1) → K) :
    (gen f).natDegree ≤ r := by sorry
