-- Prove2me | Theorems.Thm_GlobalTheory_quasiIso_tensorLeft_of_flat
-- name    : GlobalTheory.quasiIso_tensorLeft_of_flat
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:15:05.21981+00:00
-- url     : https://prove2.me/theorems/571c46c0-53da-4858-b9f0-eecad6d526a3
-- title:
--   Global Theory: quasi Iso tensor Left of flat
-- statement:
--   The Global Theory construction uses the quasi Iso tensor Left of flat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsFiniteProjectiveComplexQuasiIso.lean#L486-L491
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsFiniteProjectiveComplexQuasiIso.lean#L486-L491

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsFiniteProjectiveComplexQuasiIso
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory TensorProduct
universe u v w
open GlobalTheory
open Limits
variable {R : Type u} [CommRing R]

theorem GlobalTheory.quasiIso_tensorLeft_of_flat {K C : CochainComplex (ModuleCat.{u} R) ℕ} (φ : K ⟶ C)
    [QuasiIso φ] (hK : ∀ p, Module.Flat R (K.X p)) (hC : ∀ p, Module.Flat R (C.X p)) (n : ℕ)
    (hnK : ∀ p, n < p → IsZero (K.X p)) (hnC : ∀ p, n < p → IsZero (C.X p))
    (M : ModuleCat.{u} R) :
    QuasiIso (((MonoidalCategory.tensorLeft M).mapHomologicalComplex _).map φ) := by sorry
