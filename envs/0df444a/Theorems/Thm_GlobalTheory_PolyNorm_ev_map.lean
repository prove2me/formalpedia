-- Prove2me | Theorems.Thm_GlobalTheory_PolyNorm_ev_map
-- name    : GlobalTheory.PolyNorm.ev_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:28:31.406811+00:00
-- url     : https://prove2.me/theorems/1c43a41f-a490-43d3-8994-61d898b34ade
-- title:
--   Poly Norm: ev map
-- statement:
--   The Poly Norm construction uses the ev map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/EqProdOfMul.lean#L14-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/EqProdOfMul.lean#L14-L20

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

theorem GlobalTheory.PolyNorm.ev_map {r : ℕ} (Φ : MvPolynomial (Fin r) ℚ) {K L : Type} [CommRing K] [Algebra ℚ K]
    [CommRing L] [Algebra ℚ L] (φ : K →+* L) (F : K[X]) : φ (ev Φ F) = ev Φ (F.map φ) := by sorry
