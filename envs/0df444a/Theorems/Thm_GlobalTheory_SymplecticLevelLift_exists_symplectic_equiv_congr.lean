-- Prove2me | Theorems.Thm_GlobalTheory_SymplecticLevelLift_exists_symplectic_equiv_congr
-- name    : GlobalTheory.SymplecticLevelLift.exists_symplectic_equiv_congr
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T20:26:06.281668+00:00
-- url     : https://prove2.me/theorems/241ea4df-d05b-4937-b8a7-6893457e66b2
-- title:
--   Symplectic Level Lift: exists symplectic equiv congr
-- statement:
--   The Symplectic Level Lift construction uses the exists symplectic equiv congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSymplecticBasisCongrLevelMod.lean#L26-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSymplecticBasisCongrLevelMod.lean#L26-L71

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_GeomIntSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SymplecticZmodLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSymplecticBasisCongrLevelMod
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.SymplecticLevelLift
open Matrix Module

theorem GlobalTheory.SymplecticLevelLift.exists_symplectic_equiv_congr : ∀ (h k : ℕ) (M : Type) [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M] (Ef : LinearMap.BilinForm ℤ M) (l : (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] M), 0 < k → Module.finrank ℤ M = 2 * h → (∀ x, Ef x x = 0) → Function.Bijective Ef → (∀ a b, (k : ℤ) ∣ Ef (l a) (l b) - omegaStd a b) → ∃ B : (Fin h ⊕ Fin h → ℤ) ≃ₗ[ℤ] M, (∀ a b, Ef (B a) (B b) = omegaStd a b) ∧ ∀ a, ∃ m : M, l a - B a = (k : ℤ) • m := by sorry
