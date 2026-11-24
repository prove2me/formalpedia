-- Prove2me | Theorems.Thm_GlobalTheory_GeomFibre_finite_of_finite_sections
-- name    : GlobalTheory.GeomFibre.finite_of_finite_sections
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T13:55:53.773919+00:00
-- url     : https://prove2.me/theorems/c188dc22-6988-4a1c-826d-2383cf401786
-- title:
--   Geom Fibre: finite of finite sections
-- statement:
--   The Geom Fibre construction uses the finite of finite sections property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LocallyQuasiFiniteOfFiniteGeometricFibres.lean#L9-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LocallyQuasiFiniteOfFiniteGeometricFibres.lean#L9-L20

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocallyQuasiFiniteOfFiniteGeometricFibres
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.GeomFibre

theorem GlobalTheory.GeomFibre.finite_of_finite_sections {K : Type} [Field K] [IsAlgClosed K] {P : Scheme.{0}}
    (g : P ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType g]
    (h : Finite {p : Spec (CommRingCat.of K) ⟶ P // p ≫ g = 𝟙 _}) : Finite P := by sorry
