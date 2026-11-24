-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ultra_exists_limit_hom
-- name    : GlobalTheory.CompanionTheory.Ultra.exists_limit_hom
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:19:22.09185+00:00
-- url     : https://prove2.me/theorems/4d24cd62-92e7-4ba0-a851-af00d905e7d7
-- title:
--   Ultra: exists limit hom
-- statement:
--   The Ultra construction uses the exists limit hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IsProperSpreadsOut.lean#L352-L380
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IsProperSpreadsOut.lean#L352-L380

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_CubeTheorem_SchemeModels
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsFiniteAffineCover
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IsProperSpreadsOut
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Filter
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ultra

theorem GlobalTheory.CompanionTheory.Ultra.exists_limit_hom {R₀ R : Type} [CommRing R₀] [CommRing R] (φ : R₀ →+* R) {S₀ : Set R₀}
    (hS₀ : Algebra.adjoin ℤ S₀ = ⊤) {V : Finset R → Type} [∀ F, CommRing (V F)]
    (β : ∀ F, lvl φ S₀ F →+* V F) (U : Ultrafilter (Finset R))
    (hU : (U : Filter (Finset R)) ≤ atTop) :
    ∃ ρ : R →+* Ult U V, ∀ r, ρ (φ r) = mk U (fun F => β F (lvlHom φ hS₀ F r)) := by sorry
