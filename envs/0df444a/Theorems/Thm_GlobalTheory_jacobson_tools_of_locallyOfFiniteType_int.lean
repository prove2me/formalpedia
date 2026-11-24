-- Prove2me | Theorems.Thm_GlobalTheory_jacobson_tools_of_locallyOfFiniteType_int
-- name    : GlobalTheory.jacobson_tools_of_locallyOfFiniteType_int
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:02:57.861336+00:00
-- url     : https://prove2.me/theorems/ab5ce4e6-f93c-4ea8-b099-d809fc5f99b2
-- title:
--   Global Theory: jacobson tools of locally Of Finite Type int
-- statement:
--   The Global Theory construction uses the jacobson tools of locally Of Finite Type int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/FiniteResidueFieldOfIsClosedOfLocallyOfFiniteTyp.lean#L92-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/FiniteResidueFieldOfIsClosedOfLocallyOfFiniteTyp.lean#L92-L111

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRatA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FiniteResidueFieldOfIsClosedOfLocallyOfFiniteTyp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory

theorem GlobalTheory.jacobson_tools_of_locallyOfFiniteType_int :
    ∀ (X : Scheme.{0}) (π : X ⟶ Sp ℤ) [LocallyOfFiniteType π], JacobsonSpace X ∧
      (∀ x : X, IsClosed ({x} : Set X) → Finite (X.residueField x)) ∧
      (∀ U V : X.Opens, (∀ x : X, IsClosed ({x} : Set X) → (x ∈ U ↔ x ∈ V)) → U = V) ∧
      (∀ (ξ : X) (ι : Type) [Finite ι] (U : ι → X.Opens) (W : X.Opens), ξ ∈ W →
        ∃ x : X, IsClosed ({x} : Set X) ∧ ξ ⤳ x ∧ x ∈ W ∧ ∀ i, x ∈ U i ↔ ξ ∈ U i) ∧
      (∀ (ι : Type) [Finite ι] (Sg : ι → Set X), IrreducibleSpace X →
        (∀ x : X, IsClosed ({x} : Set X) → ∃ i, x ∈ Sg i) → ∃ i, Dense (Sg i)) := by sorry
