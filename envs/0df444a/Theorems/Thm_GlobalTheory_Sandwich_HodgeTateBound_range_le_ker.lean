-- Prove2me | Theorems.Thm_GlobalTheory_Sandwich_HodgeTateBound_range_le_ker
-- name    : GlobalTheory.Sandwich.HodgeTateBound.range_le_ker
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:21:41.7898+00:00
-- url     : https://prove2.me/theorems/48e162dd-9e58-5cee-afa4-830fa1064c9f
-- title:
--   Hodge Tate Bound: range le ker
-- statement:
--   The Hodge Tate Bound construction uses the range le ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SmulMemRange.lean#L38-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SmulMemRange.lean#L38-L47

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_CotangentSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_CyclicRecursionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_XiMulNu
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FontaineAinfLocalDomainXiAdicOrderStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SmulMemRange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PGsh.Up GlobalTheory.Sandwich Matrix
open GlobalTheory GlobalTheory.Sandwich GlobalTheory.Sandwich.HodgeTateBound
variable {A O : Type} [CommRing A] [CommRing O] {h : ℕ}

theorem GlobalTheory.Sandwich.HodgeTateBound.range_le_ker (θ : A →+* O) {F G : Matrix (Fin h) (Fin h) A} {μ : A} (hμ : θ μ = 0)
    (hGF : G * F = μ • (1 : Matrix (Fin h) (Fin h) A)) :
    LinearMap.range (Matrix.toLin' (F.map θ)) ≤ LinearMap.ker (Matrix.toLin' (G.map θ)) := by sorry
