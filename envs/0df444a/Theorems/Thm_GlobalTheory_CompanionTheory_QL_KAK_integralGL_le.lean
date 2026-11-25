-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_QL_KAK_integralGL_le
-- name    : GlobalTheory.CompanionTheory.QL.KAK.integralGL_le
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:52:10.424889+00:00
-- url     : https://prove2.me/theorems/7d6d4a2d-5e9f-5198-94ad-6e00382f6fd3
-- title:
--   KAK: integral GL le
-- statement:
--   The KAK construction uses the integral GL le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/CartanDecompositionGeneralLinear.lean#L30-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/CartanDecompositionGeneralLinear.lean#L30-L32

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

theorem GlobalTheory.CompanionTheory.QL.KAK.integralGL_le (n : ℕ) :
    GroundTheory.Automorphic.GLnLocal.integralGL F n ≤ GLint 𝒪[F] n := by sorry
