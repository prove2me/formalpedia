-- Prove2me | Theorems.Thm_GlobalTheory_TripleIntertwiner_sum_refine
-- name    : GlobalTheory.TripleIntertwiner.sum_refine
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T21:12:17.32507+00:00
-- url     : https://prove2.me/theorems/9e1a5ef3-c30a-4685-9174-6ea684c5bea4
-- title:
--   Triple Intertwiner: sum refine
-- statement:
--   The Triple Intertwiner construction uses the sum refine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/GaussPowFourHom.lean#L103-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/GaussPowFourHom.lean#L103-L133

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GaussPowFourHom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.TripleIntertwiner
open Classical
variable {V : Type*} [AddCommGroup V]

theorem GlobalTheory.TripleIntertwiner.sum_refine {F : Type} [AddCommMonoid F] {A₀ A B : AddSubgroup V} (hB : A₀ ≤ B)
    [Fintype (A ⧸ A₀.addSubgroupOf A)] [Fintype (A ⧸ B.addSubgroupOf A)] (g : V → F)
    (hg : ∀ x ∈ A, ∀ l ∈ A, l ∈ B → g (x + l) = g x) :
    ∃ k : ℕ, k * B.relIndex A = A₀.relIndex A ∧
      ∑ q : A ⧸ A₀.addSubgroupOf A, g (rep q) = k • ∑ q : A ⧸ B.addSubgroupOf A, g (rep q) := by sorry
