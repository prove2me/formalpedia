-- Prove2me | Theorems.Thm_GlobalTheory_PolyNorm_gen_map
-- name    : GlobalTheory.PolyNorm.gen_map
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T18:51:10.433009+00:00
-- url     : https://prove2.me/theorems/d7b485b2-5199-4162-80fd-dd5a747a0aa4
-- title:
--   Poly Norm: gen map
-- statement:
--   The Poly Norm construction uses the gen map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/EqProdOfMul.lean#L22-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/EqProdOfMul.lean#L22-L24

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

theorem GlobalTheory.PolyNorm.gen_map {r : ℕ} {K L : Type} [CommRing K] [CommRing L] (φ : K →+* L) (f : Fin r → K) :
    (gen f).map φ = gen (fun i => φ (f i)) := by sorry
