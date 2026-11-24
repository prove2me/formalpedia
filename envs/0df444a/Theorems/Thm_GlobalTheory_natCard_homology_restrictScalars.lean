-- Prove2me | Theorems.Thm_GlobalTheory_natCard_homology_restrictScalars
-- name    : GlobalTheory.natCard_homology_restrictScalars
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:11:57.245309+00:00
-- url     : https://prove2.me/theorems/1bc608e6-b5c6-4879-889f-b17147863c33
-- title:
--   Global Theory: nat Card homology restrict Scalars
-- statement:
--   The Global Theory construction uses the nat Card homology restrict Scalars property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NatCardHomologyRestrictScalars.lean#L6-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NatCardHomologyRestrictScalars.lean#L6-L12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NatCardHomologyRestrictScalars
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits
open GlobalTheory

theorem GlobalTheory.natCard_homology_restrictScalars {R S : Type} [CommRing R] [CommRing S] (f : R →+* S)
    (D : CochainComplex (ModuleCat.{0} S) ℕ) (n : ℕ) :
    Nat.card ((((ModuleCat.restrictScalars.{0} f).mapHomologicalComplex (ComplexShape.up ℕ)).obj D).homology n) = Nat.card (D.homology n) := by sorry
