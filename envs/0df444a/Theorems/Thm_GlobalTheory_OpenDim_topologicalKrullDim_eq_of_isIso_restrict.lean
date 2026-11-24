-- Prove2me | Theorems.Thm_GlobalTheory_OpenDim_topologicalKrullDim_eq_of_isIso_restrict
-- name    : GlobalTheory.OpenDim.topologicalKrullDim_eq_of_isIso_restrict
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T19:59:07.08812+00:00
-- url     : https://prove2.me/theorems/58986d07-f136-43db-9205-68986544d251
-- title:
--   Open Dim: topological Krull Dim eq of is Iso restrict
-- statement:
--   The Open Dim construction uses the topological Krull Dim eq of is Iso restrict property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TopologicalKrullDimEqOfIsIsoRestrict.lean#L74-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TopologicalKrullDimEqOfIsIsoRestrict.lean#L74-L92

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__GeometricallyConnectedOfIsIsoRestrict_f3ea578707b0384e
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RingKrullDimQuotientEqOfMemMinimalPrimes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TopologicalKrullDimEqOfIsIsoRestrict
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.OpenDim

theorem GlobalTheory.OpenDim.topologicalKrullDim_eq_of_isIso_restrict : ∀ (F : Type) [Field F] (W W' : Scheme.{0})
    [IsIntegral W] [IsIntegral W'] (p : W ⟶ Sp F) (q : W' ⟶ Sp F) (h : W' ⟶ W),
    LocallyOfFiniteType p → LocallyOfFiniteType q → h ≫ p = q → ∀ U : W.Opens,
    (U : Set W).Nonempty → IsIso (h ∣_ U) → topologicalKrullDim W' = topologicalKrullDim W := by sorry
