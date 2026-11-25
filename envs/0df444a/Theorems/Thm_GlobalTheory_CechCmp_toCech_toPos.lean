-- Prove2me | Theorems.Thm_GlobalTheory_CechCmp_toCech_toPos
-- name    : GlobalTheory.CechCmp.toCech_toPos
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T15:50:35.714909+00:00
-- url     : https://prove2.me/theorems/8f48f863-bc31-5d2b-9526-1117143b3e57
-- title:
--   Cech Cmp: to Cech to Pos
-- statement:
--   The Cech Cmp construction uses the to Cech to Pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PosetToCechCechToPosetCocycleEq.lean#L12-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PosetToCechCechToPosetCocycleEq.lean#L12-L38

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RestrictCapFBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PosetToCechCechToPosetCocycleEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KS (rsT IsCoc IsCob)
open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechCmp
set_option autoImplicit false
open GlobalTheory GlobalTheory.CechCmp

theorem GlobalTheory.CechCmp.toCech_toPos : ∀ (I : Type) [Finite I] (X : Scheme.{0}) (R : Type) [CommRing R] (s : X ⟶ Sp R) (U : I → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) (hinf : ∀ V W : X.Opens, IsAffineOpen V → IsAffineOpen W → IsAffineOpen (V ⊓ W)), ∀ c : GlobalTheory.KS.C1 U, IsCoc U c → toCech s U hU hinf (toPos s U hU hinf c) = c := by sorry
