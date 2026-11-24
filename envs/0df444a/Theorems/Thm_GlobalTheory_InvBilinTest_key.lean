-- Prove2me | Theorems.Thm_GlobalTheory_InvBilinTest_key
-- name    : GlobalTheory.InvBilinTest.key
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T17:19:58.535087+00:00
-- url     : https://prove2.me/theorems/3033d8e4-2a20-4c3d-bb97-ed7d989c2b19
-- title:
--   Inv Bilin Test: key
-- statement:
--   The Inv Bilin Test construction uses the key property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsLocallyConstantCosetInd.lean#L81-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsLocallyConstantCosetInd.lean#L81-L112

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHilbertSchmidtOfFiniteDimensional
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsLocallyConstantCosetInd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.OpTrace
noncomputable section
open GlobalTheory GlobalTheory.InvBilinTest
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
variable [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsHaarMeasure]
  {V : Type} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ G V}
  {Y : Type} [AddCommGroup Y] [Module ℂ Y]

theorem GlobalTheory.InvBilinTest.key [μ.IsMulRightInvariant] (hπ : IsSmooth π) (B : SB G →ₗ[ℂ] V →ₗ[ℂ] Y)
    (hB : ∀ (g : G) (φ ψ : SB G) (v : V), (∀ x, ψ.1 x = φ.1 (x * g)) → B ψ (π g v) = B φ v)
    (K : Subgroup G) (ho : IsOpen (K : Set G)) (hK : IsCompact (K : Set G))
    (φ : SB G) (hφ : ∀ k ∈ K, ∀ g, φ.1 (k * g) = φ.1 g) (v : V) :
    B (cosetInd K ho hK 1) (smoothOp π μ φ.1 v) = (μ.real K : ℂ) • B φ v := by sorry
