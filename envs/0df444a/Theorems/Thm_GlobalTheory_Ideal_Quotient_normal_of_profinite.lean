-- Prove2me | Theorems.Thm_GlobalTheory_Ideal_Quotient_normal_of_profinite
-- name    : GlobalTheory.Ideal.Quotient.normal_of_profinite
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T17:12:03.168271+00:00
-- url     : https://prove2.me/theorems/ee4c6750-edf9-45fa-b404-ddca86a800f7
-- title:
--   Quotient: normal of profinite
-- statement:
--   The Quotient construction uses the normal of profinite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ResidueNormalOfProfiniteInvariants.lean#L9-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ResidueNormalOfProfiniteInvariants.lean#L9-L39

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ResidueNormalOfProfiniteInvariants
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
attribute [local instance] Subgroup.finiteIndex_of_finite_quotient
open Polynomial

theorem GlobalTheory.Ideal.Quotient.normal_of_profinite : ∀ {A B : Type} [CommRing A] [CommRing B] [Algebra A B] (G : Type) [Group G] [MulSemiringAction G B] [SMulCommClass G A B] [TopologicalSpace G] [CompactSpace G] [TotallyDisconnectedSpace G] [IsTopologicalGroup G] [TopologicalSpace B] [DiscreteTopology B] [ContinuousSMul G B] [Algebra.IsInvariant A B G] (P : Ideal A) (Q : Ideal B) [Q.LiesOver P] [P.IsMaximal] [Q.IsMaximal], letI := Ideal.Quotient.field P; letI := Ideal.Quotient.field Q; Normal (A ⧸ P) (B ⧸ Q) := by sorry
