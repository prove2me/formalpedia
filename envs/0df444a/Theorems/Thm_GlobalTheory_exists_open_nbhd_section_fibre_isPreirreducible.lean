-- Prove2me | Theorems.Thm_GlobalTheory_exists_open_nbhd_section_fibre_isPreirreducible
-- name    : GlobalTheory.exists_open_nbhd_section_fibre_isPreirreducible
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:38:44.858829+00:00
-- url     : https://prove2.me/theorems/64f788f2-8e97-44d3-9f6e-e7c828c34f36
-- title:
--   Global Theory: exists open nbhd section fibre is Preirreducible
-- statement:
--   The Global Theory construction uses the exists open nbhd section fibre is Preirreducible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsOpenNbhdSectionFibreIsPreirreducible.lean#L14-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsOpenNbhdSectionFibreIsPreirreducible.lean#L14-L93

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAffineChartPreirreducibleFiberStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PreirreducibleSpaceTensorOfPullbackStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsBasicOpenFibresPreirreducibleSmoothStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOpenNbhdSectionFibreIsPreirreducible
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
open GlobalTheory

theorem GlobalTheory.exists_open_nbhd_section_fibre_isPreirreducible : ∀ (X S : Scheme.{0}) (f : X ⟶ S) (e : S ⟶ X),
    Smooth f → e ≫ f = 𝟙 _ → ∀ s : S, ∃ (U : X.Opens) (V₀ V : S.Opens) (I : Finset Γ(S, V)),
      V₀ ≤ V ∧ s ∈ V₀ ∧ e s ∈ U ∧ (∀ c ∈ I, s ∉ S.basicOpen c) ∧
      ∀ t ∈ V₀, (∀ c ∈ I, t ∉ S.basicOpen c) → IsPreirreducible ((U : Set X) ∩ f ⁻¹' {t}) := by sorry
