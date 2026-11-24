-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_LGroupSection_exists_isLocallyConstant_mem
-- name    : GlobalTheory.CompanionTheory.LGroupSection.exists_isLocallyConstant_mem
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T11:52:42.558799+00:00
-- url     : https://prove2.me/theorems/50c3e25c-7926-479e-a3be-7217fe489c34
-- title:
--   LGroup Section: exists is Locally Constant mem
-- statement:
--   The LGroup Section construction uses the exists is Locally Constant mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsContinuousSectionQuotient.lean#L33-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsContinuousSectionQuotient.lean#L33-L49

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsContinuousSectionQuotient
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Topology Filter Set
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.LGroupSection
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem GlobalTheory.CompanionTheory.LGroupSection.exists_isLocallyConstant_mem {X : Type*} [TopologicalSpace X] (V : ℕ → Set X)
    (hV : ∀ n, IsClopen (V n)) (hcov : ∀ x, ∃ n, x ∈ V n) :
    ∃ f : X → ℕ, IsLocallyConstant f ∧ ∀ x, x ∈ V (f x) := by sorry
