-- Prove2me | Theorems.Thm_GlobalTheory_TorusConst_ev_eq
-- name    : GlobalTheory.TorusConst.ev_eq
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T21:09:19.64226+00:00
-- url     : https://prove2.me/theorems/3b8bd0a2-fb85-4e96-af85-fd0a932d3a2e
-- title:
--   Torus Const: ev eq
-- statement:
--   The Torus Const construction uses the ev eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SplitTorusToAbelianVarietyConst.lean#L399-L424
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SplitTorusToAbelianVarietyConst.lean#L399-L424

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SplitTorusHomProperTrivialField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SplitTorusToAbelianVarietyConst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open GlobalTheory.TorusConst
open Polynomial TorusToProper
variable {K : Type} [Field K] {B : Over (Spec (CommRingCat.of K))}
open LaurentPolynomial
variable {L : Type} [Field L] [Algebra K L]

theorem GlobalTheory.TorusConst.ev_eq [GrpObj B] [IsProper B.hom] (u : sp K L[T;T⁻¹] ⟶ B) (x y : Lˣ) :
    spm (ev (AlgHom.id K L) x) ≫ u = spm (ev (AlgHom.id K L) y) ≫ u := by sorry
