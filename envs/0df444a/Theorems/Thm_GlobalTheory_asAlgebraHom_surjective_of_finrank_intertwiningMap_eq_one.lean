-- Prove2me | Theorems.Thm_GlobalTheory_asAlgebraHom_surjective_of_finrank_intertwiningMap_eq_one
-- name    : GlobalTheory.asAlgebraHom_surjective_of_finrank_intertwiningMap_eq_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:24:22.069804+00:00
-- url     : https://prove2.me/theorems/43b97a4d-0e3a-48c6-9eb8-5d5717e8efa9
-- title:
--   Global Theory: as Algebra Hom surjective of finrank intertwining Map eq one
-- statement:
--   The Global Theory construction uses the as Algebra Hom surjective of finrank intertwining Map eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/AsAlgebraHomSurjectiveOfFinrankIntertwiningMapEq.lean#L7-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/AsAlgebraHomSurjectiveOfFinrankIntertwiningMapEq.lean#L7-L38

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_AsAlgebraHomSurjectiveOfFinrankIntertwiningMapEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open scoped MonoidAlgebra

theorem GlobalTheory.asAlgebraHom_surjective_of_finrank_intertwiningMap_eq_one :
    ∀ (K : Type) [Field K] [CharZero K] (G : Type) [Group G] [Finite G] (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (τ : Representation K G V), Module.finrank K (Representation.IntertwiningMap τ τ) = 1 → Nontrivial V ∧ Function.Surjective τ.asAlgebraHom := by sorry
