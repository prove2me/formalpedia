-- Prove2me | Theorems.Thm_GlobalTheory_Sandwich_HodgeTateBound_smul_mem_range
-- name    : GlobalTheory.Sandwich.HodgeTateBound.smul_mem_range
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:22:22.365971+00:00
-- url     : https://prove2.me/theorems/e847c59f-8551-4b33-a8ff-db3da238d030
-- title:
--   Hodge Tate Bound: smul mem range
-- statement:
--   The Hodge Tate Bound construction uses the smul mem range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SmulMemRange.lean#L49-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SmulMemRange.lean#L49-L76

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

theorem GlobalTheory.Sandwich.HodgeTateBound.smul_mem_range [IsDomain A] (θ : A →+* O) (hs : Function.Surjective θ) {ξ ν μ : A}
    (hker : RingHom.ker θ = Ideal.span {ξ}) (hξ : ξ ≠ 0) (hμ : ξ * ν = μ)
    {F G : Matrix (Fin h) (Fin h) A} (hFG : F * G = μ • (1 : Matrix (Fin h) (Fin h) A))
    (f : Fin h → O) (hf : f ∈ LinearMap.ker (Matrix.toLin' (G.map θ))) :
    θ ν • f ∈ LinearMap.range (Matrix.toLin' (F.map θ)) := by sorry
