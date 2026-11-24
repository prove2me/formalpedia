-- Prove2me | Theorems.Thm_GlobalTheory_DenseClosedAffineSubsets_mem_basicOpen_of_mul_eq_one
-- name    : GlobalTheory.DenseClosedAffineSubsets.mem_basicOpen_of_mul_eq_one
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T12:43:21.923798+00:00
-- url     : https://prove2.me/theorems/ff3a6575-f386-4534-b522-5928549a6704
-- title:
--   Dense Closed Affine Subsets: mem basic Open of mul eq one
-- statement:
--   The Dense Closed Affine Subsets construction uses the mem basic Open of mul eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsAffineLeOrDisjoint.lean#L324-L353
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsAffineLeOrDisjoint.lean#L324-L353

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_BaseIdealIdeal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAffineLeOrDisjoint
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open GlobalTheory GlobalTheory.DenseClosedAffineSubsets
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] MvPolynomial.gradedAlgebra

theorem GlobalTheory.DenseClosedAffineSubsets.mem_basicOpen_of_mul_eq_one {W P X : Scheme.{0}} (U O : W.Opens) (hUO : U ≤ O)
    (φ : U.toScheme ⟶ P) (π : X ⟶ W) (q : X ⟶ P)
    (j : U.toScheme ⟶ X) [IsSchemeTheoreticallyDominant j] [QuasiCompact j]
    (h₁ : j ≫ π = U.ι) (h₂ : j ≫ q = φ) (g : Γ(O.toScheme, ⊤))
    (D : P.Opens) (r : Γ(D.toScheme, ⊤))
    (hr : ∀ (V : Scheme.{0}) (a : V ⟶ U) (b : V ⟶ D), a ≫ φ = b ≫ D.ι →
      b.appTop r * a.appTop ((W.homOfLE hUO).appTop g) = 1)
    (x : X) (hO : π x ∈ O) (hD : q x ∈ D) :
    ∃ z : D.toScheme, z ∈ D.toScheme.basicOpen r ∧ D.ι z = q x := by sorry
