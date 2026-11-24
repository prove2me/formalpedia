-- Prove2me | Theorems.Thm_GlobalTheory_Chevalley_isArtinian_quotient_smul_top
-- name    : GlobalTheory.Chevalley.isArtinian_quotient_smul_top
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:10:25.033842+00:00
-- url     : https://prove2.me/theorems/acec8d9b-4a53-4ca1-96c2-201a268ac67c
-- title:
--   Chevalley: is Artinian quotient smul top
-- statement:
--   The Chevalley construction uses the is Artinian quotient smul top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsLeMaximalIdealPowSmulOfDirected.lean#L27-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsLeMaximalIdealPowSmulOfDirected.lean#L27-L33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FiniteCocycles
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MatMapTmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsLeMaximalIdealPowSmulOfDirected
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Polynomial IsLocalRing GlobalTheory.Pat
open GlobalTheory GlobalTheory.Chevalley

theorem GlobalTheory.Chevalley.isArtinian_quotient_smul_top (B M : Type) [CommRing B] [IsLocalRing B]
    [IsNoetherianRing B] [AddCommGroup M] [Module B M] [Module.Finite B M] (k : ℕ) :
    IsArtinian B (M ⧸ (maximalIdeal B ^ k • (⊤ : Submodule B M))) := by sorry
