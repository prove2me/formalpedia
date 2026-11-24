-- Prove2me | Theorems.Thm_GlobalTheory_PBasis_indep_sUnion
-- name    : GlobalTheory.PBasis.indep_sUnion
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T18:38:37.156279+00:00
-- url     : https://prove2.me/theorems/bd64d040-d216-4b23-a8e5-1b083cf42092
-- title:
--   PBasis: indep s Union
-- statement:
--   The PBasis construction uses the indep s Union property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/GraphRingMono.lean#L43-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/GraphRingMono.lean#L43-L61

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_GraphRingMono
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing Polynomial
open GlobalTheory GlobalTheory.PBasis
variable {k : Type} [Field k]

theorem GlobalTheory.PBasis.indep_sUnion (p : ℕ) (c : Set (Set k)) (hc : IsChain (· ⊆ ·) c) (hne : c.Nonempty)
    (h : ∀ B ∈ c, Indep p B) : Indep p (⋃₀ c) := by sorry
