-- Prove2me | Theorems.Thm_GlobalTheory_cube_cut_regular_sequence
-- name    : GlobalTheory.cube_cut_regular_sequence
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:14:50.224899+00:00
-- url     : https://prove2.me/theorems/9eda726a-ffb2-48ab-8b61-4ddfad8115cb
-- title:
--   Global Theory: cube cut regular sequence
-- statement:
--   The Global Theory construction uses the cube cut regular sequence property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/CubeCutRegularSequence.lean#L175-L214
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/CubeCutRegularSequence.lean#L175-L214

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_CubeCutRegularSequence
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory GlobalTheory
open GlobalTheory
open CubeCut

theorem GlobalTheory.cube_cut_regular_sequence : ∀ (K : Type) [CommRing K] (I : Type) [LinearOrder I] [Fintype I] (g : ℕ) (n : ℤ) (C : ℤ → Cube.{0} I K) (mu : Fin g → ∀ l l', C l ⟶ C l'), 0 < n → (∀ i j l l' l'', l' = l + n → l'' = l' + n → mu i l l' ≫ mu j l' l'' = mu j l l' ≫ mu i l' l'') → (∀ (T : Finset I), T.Nonempty → ∀ (i : Fin g) (l l' : ℤ) (y : (C l).obj T), l' = l + n → ((mu i l l').app T).hom y ∈ (⨆ (j : Fin g) (_ : (j : ℕ) < i), LinearMap.range ((mu j l l').app T).hom) → y ∈ ⨆ (j : Fin g) (_ : (j : ℕ) < i), LinearMap.range ((mu j (l - n) l).app T).hom) → (∀ l, 0 < l → ∀ p, (cubeComplex (C l)).ExactAt p) → (∀ (i : Fin g) (l l' : ℤ) (y : (C l).obj ∅), l' = l + n → (i : ℕ) * n < l → ((mu i l l').app ∅).hom y ∈ (⨆ (j : Fin g) (_ : (j : ℕ) < i), LinearMap.range ((mu j l l').app ∅).hom) → y ∈ ⨆ (j : Fin g) (_ : (j : ℕ) < i), LinearMap.range ((mu j (l - n) l).app ∅).hom) ∧ ∀ l : ℤ, g * n < l → (∀ y : (C l).obj ∅, (∀ a : I, Cube.res (C l) (Finset.empty_subset {a}) y ∈ ⨆ (j : Fin g) (_ : (j : ℕ) < g), LinearMap.range ((mu j (l - n) l).app {a}).hom) → y ∈ ⨆ (j : Fin g) (_ : (j : ℕ) < g), LinearMap.range ((mu j (l - n) l).app ∅).hom) ∧ ∀ y : ∀ a : I, (C l).obj {a}, (∀ a a' : I, Cube.res (C l) (show ({a} : Finset I) ⊆ {a, a'} by simp) (y a) - Cube.res (C l) (show ({a'} : Finset I) ⊆ {a, a'} by simp) (y a') ∈ ⨆ (j : Fin g) (_ : (j : ℕ) < g), LinearMap.range ((mu j (l - n) l).app {a, a'}).hom) → ∃ y₀ : (C l).obj ∅, ∀ a, Cube.res (C l) (Finset.empty_subset {a}) y₀ - y a ∈ ⨆ (j : Fin g) (_ : (j : ℕ) < g), LinearMap.range ((mu j (l - n) l).app {a}).hom := by sorry
