-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_QL_KAK_dg_mem
-- name    : GlobalTheory.CompanionTheory.QL.KAK.dg_mem
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:52:12.372943+00:00
-- url     : https://prove2.me/theorems/bebb2ba6-dc89-5c16-8c10-e65789e5c287
-- title:
--   KAK: dg mem
-- statement:
--   The KAK construction uses the dg mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/CartanDecompositionGeneralLinear.lean#L16-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/CartanDecompositionGeneralLinear.lean#L16-L26

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

theorem GlobalTheory.CompanionTheory.QL.KAK.dg_mem (O : Subring F) {n : ℕ} (a : Fin n → Fˣ) (h₁ : ∀ i, (a i : F) ∈ O)
    (h₂ : ∀ i, (((a i)⁻¹ : Fˣ) : F) ∈ O) : dg a ∈ GLint O n := by sorry
