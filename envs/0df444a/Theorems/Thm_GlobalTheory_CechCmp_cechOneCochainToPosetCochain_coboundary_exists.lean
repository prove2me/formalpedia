-- Prove2me | Theorems.Thm_GlobalTheory_CechCmp_cechOneCochainToPosetCochain_coboundary_exists
-- name    : GlobalTheory.CechCmp.cechOneCochainToPosetCochain_coboundary_exists
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T16:30:33.410032+00:00
-- url     : https://prove2.me/theorems/b29a8ff9-5280-5a03-99b3-4bfddd1371ad
-- title:
--   Cech Cmp: cech One Cochain To Poset Cochain coboundary exists
-- statement:
--   The Cech Cmp construction uses the cech One Cochain To Poset Cochain coboundary exists property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CechOneCochainToPosetCochainCoboundaryExists.lean#L15-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CechOneCochainToPosetCochainCoboundaryExists.lean#L15-L29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RestrictCapFBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CechOneCochainToPosetCochainCoboundaryExists
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
open GlobalTheory.KS (rsT IsCoc IsCob)
open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechCmp
open GlobalTheory GlobalTheory.CechCmp

theorem GlobalTheory.CechCmp.cechOneCochainToPosetCochain_coboundary_exists : ∀ (I : Type) [Finite I] (X : Scheme.{0}) (R : Type) [CommRing R] (s : X ⟶ Sp R)
    (U : I → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (hinf : ∀ V W : X.Opens, IsAffineOpen V → IsAffineOpen W → IsAffineOpen (V ⊓ W)),
    ∀ c : GlobalTheory.KS.C1 U, IsCob U c → ∃ g, d0 (capF s U hU hinf) g = toPos s U hU hinf c := by sorry
