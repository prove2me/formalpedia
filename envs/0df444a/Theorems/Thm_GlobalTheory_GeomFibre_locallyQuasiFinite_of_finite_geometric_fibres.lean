-- Prove2me | Theorems.Thm_GlobalTheory_GeomFibre_locallyQuasiFinite_of_finite_geometric_fibres
-- name    : GlobalTheory.GeomFibre.locallyQuasiFinite_of_finite_geometric_fibres
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:06:29.553796+00:00
-- url     : https://prove2.me/theorems/9ab30f0b-37d1-58bf-862b-3f222f0634c6
-- title:
--   Geom Fibre: locally Quasi Finite of finite geometric fibres
-- statement:
--   The Geom Fibre construction uses the locally Quasi Finite of finite geometric fibres property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LocallyQuasiFiniteOfFiniteGeometricFibres.lean#L22-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LocallyQuasiFiniteOfFiniteGeometricFibres.lean#L22-L48

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

theorem GlobalTheory.GeomFibre.locallyQuasiFinite_of_finite_geometric_fibres :
    ∀ (X Y : Scheme.{0}) (f : X ⟶ Y), LocallyOfFiniteType f →
      (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ X),
        Set.Finite {y : Sp K ⟶ X | y ≫ f = x ≫ f}) → LocallyQuasiFinite f := by sorry
