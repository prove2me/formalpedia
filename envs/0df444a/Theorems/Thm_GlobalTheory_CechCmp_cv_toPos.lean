-- Prove2me | Theorems.Thm_GlobalTheory_CechCmp_cv_toPos
-- name    : GlobalTheory.CechCmp.cv_toPos
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T15:33:07.431335+00:00
-- url     : https://prove2.me/theorems/97f5a777-b811-5e0a-86c1-f969756f04ee
-- title:
--   Cech Cmp: cv to Pos
-- statement:
--   The Cech Cmp construction uses the cv to Pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RestrictCapFBijective.lean#L120-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RestrictCapFBijective.lean#L120-L122

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LeISupInfPreimage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CechPullOneBijectiveLatticeCover
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RestrictCapFBijective
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
open CategoryTheory AlgebraicGeometry Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KS (rsT C1 IsCoc IsCob)
open GlobalTheory.CatCoh GlobalTheory.CechDR
open GlobalTheory GlobalTheory.CechCmp
variable {I : Type} {X : Scheme.{0}}
variable {R : Type} [CommRing R] [Finite I] (s : X ⟶ Sp R) (U : I → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
  (hinf : ∀ V W : X.Opens, IsAffineOpen V → IsAffineOpen W → IsAffineOpen (V ⊓ W))

theorem GlobalTheory.CechCmp.cv_toPos (c : C1 U) {T T' : (NE I)ᵒᵖ} (a : T ⟶ T') :
    cv s U hU hinf T' (toPos s U hU hinf c T T' a) = rsT (c T.unop.pt T'.unop.pt) (cap U T'.unop) := by sorry
