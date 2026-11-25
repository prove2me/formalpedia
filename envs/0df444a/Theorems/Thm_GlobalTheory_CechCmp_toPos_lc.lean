-- Prove2me | Theorems.Thm_GlobalTheory_CechCmp_toPos_lc
-- name    : GlobalTheory.CechCmp.toPos_lc
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T15:32:48.391827+00:00
-- url     : https://prove2.me/theorems/f72ab788-6c91-5919-bc90-6ccb713ad7cd
-- title:
--   Cech Cmp: to Pos lc
-- statement:
--   The Cech Cmp construction uses the to Pos lc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RestrictCapFBijective.lean#L147-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RestrictCapFBijective.lean#L147-L155

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
variable {I : Type} {X : Scheme.{0}} {R : Type} [CommRing R] [Finite I] (s : X ⟶ Sp R) (U : I → X.Opens)
  (hU : ∀ i, IsAffineOpen (U i)) (hinf : ∀ V W : X.Opens, IsAffineOpen V → IsAffineOpen W → IsAffineOpen (V ⊓ W))

theorem GlobalTheory.CechCmp.toPos_lc {n : ℕ} (cc : Fin n → R) (b : Fin n → C1 U) :
    toPos s U hU hinf (fun i j => ∑ a, constFn s (U i ⊓ U j) (cc a) * b a i j) =
      ∑ a, cc a • toPos s U hU hinf (b a) := by sorry
