-- Prove2me | Theorems.Thm_GlobalTheory_PolyNorm_gen_coeff
-- name    : GlobalTheory.PolyNorm.gen_coeff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:52:39.009727+00:00
-- url     : https://prove2.me/theorems/3973ebf6-58cc-4625-b888-e3952dbaa629
-- title:
--   Poly Norm: gen coeff
-- statement:
--   The Poly Norm construction uses the gen coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/EqProdOfMul.lean#L26-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/EqProdOfMul.lean#L26-L30

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

theorem GlobalTheory.PolyNorm.gen_coeff {r : ℕ} {K : Type} [CommRing K] (F : K[X]) (h : F.natDegree < r) :
    gen (fun i : Fin r => F.coeff i) = F := by sorry
