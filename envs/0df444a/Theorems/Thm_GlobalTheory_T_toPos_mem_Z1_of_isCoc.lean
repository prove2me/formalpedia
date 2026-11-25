-- Prove2me | Theorems.Thm_GlobalTheory_T_toPos_mem_Z1_of_isCoc
-- name    : GlobalTheory.T.toPos_mem_Z1_of_isCoc
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T16:02:39.296395+00:00
-- url     : https://prove2.me/theorems/9f4c2654-e155-507b-be2a-b3c6bddf803b
-- title:
--   T: to Pos mem Z1 of is Coc
-- statement:
--   The T construction uses the to Pos mem Z1 of is Coc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CechOneCochainToPosetCochainMemCocyclesStatement.lean#L10-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CechOneCochainToPosetCochainMemCocyclesStatement.lean#L10-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CechOneCochainToPosetCochainMemCocycles
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RestrictCapFBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CechOneCochainToPosetCochainMemCocyclesStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.toPos_mem_Z1_of_isCoc : ∀ (I : Type) [Finite I] (X : Scheme.{0}) (R : Type) [CommRing R] (s : X ⟶ Sp R) (U : I → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) (hinf : ∀ V W : X.Opens, IsAffineOpen V → IsAffineOpen W → IsAffineOpen (V ⊓ W)), ∀ c : GlobalTheory.KS.C1 U, IsCoc U c → toPos s U hU hinf c ∈ Z1 (capF s U hU hinf) := by sorry
