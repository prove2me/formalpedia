-- Prove2me | Theorems.Thm_GlobalTheory_AdeleBaseChange_continuous_symm_finite
-- name    : GlobalTheory.AdeleBaseChange.continuous_symm_finite
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:28:56.746126+00:00
-- url     : https://prove2.me/theorems/286dbc5e-a42a-46fb-aa96-f769c86b7fc9
-- title:
--   Adele Base Change: continuous symm finite
-- statement:
--   The Adele Base Change construction uses the continuous symm finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ContinuousSymmFinite.lean#L9-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ContinuousSymmFinite.lean#L9-L29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsOpenNsmulAdelicCompletionOfVectorSet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ContinuousSymmFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical
open scoped TensorProduct ContDiff nonZeroDivisors
open scoped Topology
open GlobalTheory GlobalTheory.AdeleBaseChange

theorem GlobalTheory.AdeleBaseChange.continuous_symm_finite : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (ι : FiniteAdeleRing (𝓞 F) F ⊗[F] E ≃+* FiniteAdeleRing (𝓞 E) E), (∀ y, y ∈ AddSubgroup.closure {y : FiniteAdeleRing (𝓞 F) F ⊗[F] E | ∃ a ∈ {a : FiniteAdeleRing (𝓞 F) F | ∀ v : HeightOneSpectrum (𝓞 F), a v ∈ v.adicCompletionIntegers F}, ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)} ↔ ∀ P, Valued.v (ι y P) ≤ 1) → letI : TopologicalSpace (FiniteAdeleRing (𝓞 F) F ⊗[F] E) := moduleTopology (FiniteAdeleRing (𝓞 F) F) (FiniteAdeleRing (𝓞 F) F ⊗[F] E); Continuous ι.symm := by sorry
