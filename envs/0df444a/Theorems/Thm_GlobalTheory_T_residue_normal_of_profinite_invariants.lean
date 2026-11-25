-- Prove2me | Theorems.Thm_GlobalTheory_T_residue_normal_of_profinite_invariants
-- name    : GlobalTheory.T.residue_normal_of_profinite_invariants
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:36:28.636236+00:00
-- url     : https://prove2.me/theorems/082f4795-d1dd-460c-aee1-d6ff8a7fcb6e
-- title:
--   T: residue normal of profinite invariants
-- statement:
--   The T construction uses the residue normal of profinite invariants property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ResidueNormalOfProfiniteInvariantsStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ResidueNormalOfProfiniteInvariantsStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ResidueNormalOfProfiniteInvariants
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ResidueNormalOfProfiniteInvariantsStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.residue_normal_of_profinite_invariants : ∀ {A B : Type} [CommRing A] [CommRing B] [Algebra A B] (G : Type) [Group G] [MulSemiringAction G B] [SMulCommClass G A B] [TopologicalSpace G] [CompactSpace G] [TotallyDisconnectedSpace G] [IsTopologicalGroup G] [TopologicalSpace B] [DiscreteTopology B] [ContinuousSMul G B] [Algebra.IsInvariant A B G] (P : Ideal A) (Q : Ideal B) [Q.LiesOver P] [P.IsMaximal] [Q.IsMaximal], letI := Ideal.Quotient.field P; letI := Ideal.Quotient.field Q; Normal (A ⧸ P) (B ⧸ Q) := by sorry
