-- Prove2me | Theorems.Thm_GlobalTheory_T_natCard_homology_restrictScalars_alt
-- name    : GlobalTheory.T.natCard_homology_restrictScalars_alt
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T20:53:56.885771+00:00
-- url     : https://prove2.me/theorems/27edf343-d358-4fa6-b11a-5c183a240d49
-- title:
--   T: nat Card homology restrict Scalars alt
-- statement:
--   The T construction uses the nat Card homology restrict Scalars alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NatCardHomologyRestrictScalarsStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NatCardHomologyRestrictScalarsStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NatCardHomologyRestrictScalars
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NatCardHomologyRestrictScalarsStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.natCard_homology_restrictScalars_alt : ∀ {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (D : CochainComplex (ModuleCat.{0} S) ℕ) (n : ℕ), Nat.card ((((ModuleCat.restrictScalars.{0} f).mapHomologicalComplex (ComplexShape.up ℕ)).obj D).homology n) = Nat.card (D.homology n) := by sorry
