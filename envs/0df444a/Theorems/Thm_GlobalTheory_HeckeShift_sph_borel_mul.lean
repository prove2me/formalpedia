-- Prove2me | Theorems.Thm_GlobalTheory_HeckeShift_sph_borel_mul
-- name    : GlobalTheory.HeckeShift.sph_borel_mul
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T14:04:53.475992+00:00
-- url     : https://prove2.me/theorems/7a29f2ca-5328-4595-9140-4b0be339350f
-- title:
--   Hecke Shift: sph borel mul
-- statement:
--   The Hecke Shift construction uses the sph borel mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/HasSumHeckeSeriesSphericalEigenfunction.lean#L84-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/HasSumHeckeSeriesSphericalEigenfunction.lean#L84-L94

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasBoundedSumsOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HasSumHeckeSeriesBorelSphericalIntegralCosetsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HasSumHeckeSeriesSphericalEigenfunction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.GLDoubling
noncomputable section
open GlobalTheory GlobalTheory.HeckeShift
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem GlobalTheory.HeckeShift.sph_borel_mul {γ : Fin n → ℂ} {φ : GL (Fin n) k → ℂ} (hφ : IsBorelSph k γ φ) (hγ : ∀ i, γ i ≠ 0)
    {b : GL (Fin n) k} (hb : b ∈ borel k (Fin n)) (h : GL (Fin n) k) :
    φ (b * h) = (∏ i, γ i ^ ord k (diagU hb i)) * φ h := by sorry
