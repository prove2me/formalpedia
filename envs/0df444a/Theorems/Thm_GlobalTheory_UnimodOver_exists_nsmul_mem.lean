-- Prove2me | Theorems.Thm_GlobalTheory_UnimodOver_exists_nsmul_mem
-- name    : GlobalTheory.UnimodOver.exists_nsmul_mem
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T21:25:16.932156+00:00
-- url     : https://prove2.me/theorems/db2404d3-a9f3-4984-9abb-09314b8a916e
-- title:
--   Unimod Over: exists nsmul mem
-- statement:
--   The Unimod Over construction uses the exists nsmul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsPolarizedSuperlatticeOfRiemannForm.lean#L43-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsPolarizedSuperlatticeOfRiemannForm.lean#L43-L54

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPolarizedSuperlatticeOfRiemannForm
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
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.UnimodOver
open Module
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

theorem GlobalTheory.UnimodOver.exists_nsmul_mem {L M : Submodule ℤ V} [DiscreteTopology M]
    (hs : Submodule.span ℝ (L : Set V) = ⊤) (h : L ≤ M) :
    ∃ N : ℕ, 0 < N ∧ ∀ x ∈ M, N • x ∈ L := by sorry
