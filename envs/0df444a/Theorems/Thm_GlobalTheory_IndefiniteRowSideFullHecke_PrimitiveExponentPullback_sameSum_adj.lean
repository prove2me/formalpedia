-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_PrimitiveExponentPullback_sameSum_adj
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.PrimitiveExponentPullback.sameSum_adj
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:10:42.239785+00:00
-- url     : https://prove2.me/theorems/6ca90fa8-de07-4376-9bfd-d79783df33f5
-- title:
--   Primitive Exponent Pullback: same Sum adj
-- statement:
--   The Primitive Exponent Pullback construction uses the same Sum adj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/PrimitiveExponentPullback.lean#L96-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/PrimitiveExponentPullback.lean#L96-L114

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_IsAbelianScheme
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubicalPullBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_HostConjugateIdeal
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_PrimitiveExponentPullback
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory
  CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.PrimitiveExponentPullback
open GlobalTheory.IndefiniteRowSideFullHecke.HostConjugateIdeal
variable {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G]

theorem GlobalTheory.IndefiniteRowSideFullHecke.PrimitiveExponentPullback.sameSum_adj (a b : G ⟶ G) [IsMonHom a] [IsMonHom b] {T : Over S} (h : T ⟶ G ⊗ G)
    (hh : h ≫ fst G G = 1 ∨ h ≫ snd G G = 1) :
    LB.SameSum (fun k => h.left ≫ adjPt G a b k) adjExp
      (PEmpty.elim : PEmpty.{1} → (T.left ⟶ G.left)) PEmpty.elim := by sorry
