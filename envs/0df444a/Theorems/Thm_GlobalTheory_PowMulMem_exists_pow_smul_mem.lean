-- Prove2me | Theorems.Thm_GlobalTheory_PowMulMem_exists_pow_smul_mem
-- name    : GlobalTheory.PowMulMem.exists_pow_smul_mem
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T06:12:05.676844+00:00
-- url     : https://prove2.me/theorems/889d2f4a-cdbc-4f9e-b5ba-efe6d3c6730d
-- title:
--   Pow Mul Mem: exists pow smul mem
-- statement:
--   The Pow Mul Mem construction uses the exists pow smul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/AlgMem.lean#L39-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/AlgMem.lean#L39-L72

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIntegralIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NcardImageOfLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_AlgMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc
open GlobalTheory GlobalTheory.PowMulMem
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem GlobalTheory.PowMulMem.exists_pow_smul_mem [IsNonarchimedeanLocalField F] [CharZero F] (L : LocE F E)
    {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) {n : ℕ} {Λ : Submodule L.O (Fin n → E)}
    (hΛ : GlobalTheory.HL.IsLat L Λ) (v : Fin n → E) :
    ∃ k : ℕ, algebraMap F E ((ϖ : F) ^ k) • v ∈ Λ := by sorry
