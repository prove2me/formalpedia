-- Prove2me | Theorems.Thm_GlobalTheory_VolFin_Den_family
-- name    : GlobalTheory.VolFin.Den.family
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:10:47.868796+00:00
-- url     : https://prove2.me/theorems/723cb362-b057-408b-9db5-b60ec2cc2290
-- title:
--   Den: family
-- statement:
--   The Den construction uses the family property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/TendstoOfSandwich.lean#L46-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/TendstoOfSandwich.lean#L46-L51

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TendstoOfSandwich
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.VolFin
open Module Filter Topology
variable {K F F' : Type} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] {ι : Type}

theorem GlobalTheory.VolFin.Den.family {R : ι → Subalgebra K F} {γ : ι → F} (h : Den R γ) {κ : Type} [Finite κ]
    (u : κ → F) : ∃ c, ∃ q ∈ piece R γ c, q ≠ 0 ∧ ∀ k, q * u k ∈ piece R γ c := by sorry
