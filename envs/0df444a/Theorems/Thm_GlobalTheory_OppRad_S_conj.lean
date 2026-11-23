-- Prove2me | Theorems.Thm_GlobalTheory_OppRad_S_conj
-- name    : GlobalTheory.OppRad.S_conj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:05:37.35783+00:00
-- url     : https://prove2.me/theorems/03c67b63-8635-448d-b7e0-c9d28fde0fa2
-- title:
--   Opp Rad: S conj
-- statement:
--   The Opp Rad construction uses the S conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MatrixRegular.lean#L75-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MatrixRegular.lean#L75-L82

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MatrixRegular
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.OppRad
open scoped Classical
variable {G V : Type} [Group G] [Finite G] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V)
variable {π}

theorem GlobalTheory.OppRad.S_conj {H K : Subgroup G} {w : G} (h1 : ∀ u ∈ H, w * u * w⁻¹ ∈ K) (h2 : ∀ u ∈ K, w⁻¹ * u * w⁻¹⁻¹ ∈ H)
    (v : V) : π w (S π H v) = S π K (π w v) := by sorry
