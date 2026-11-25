-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_QL_KAK_irreducible_pi
-- name    : GlobalTheory.CompanionTheory.QL.KAK.irreducible_pi
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:53:28.648714+00:00
-- url     : https://prove2.me/theorems/f1adc1fd-c55a-46ed-87c0-851ad22879c9
-- title:
--   KAK: irreducible pi
-- statement:
--   The KAK construction uses the irreducible pi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/CartanDecompositionGeneralLinear.lean#L34-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/CartanDecompositionGeneralLinear.lean#L34-L47

import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_GroundTheory_AutomorphicForms_Cartan
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_CartanDecompositionGeneralLinear
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QL GlobalTheory.CompanionTheory.QL.KAK
variable {F : Type} [Field F]
variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem GlobalTheory.CompanionTheory.QL.KAK.irreducible_pi {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ} (h : LF 𝒪[F] ϖ nrm q)
    (hϖ : ϖ ∈ 𝒪[F]) : Irreducible (⟨ϖ, hϖ⟩ : 𝒪[F]) := by sorry
