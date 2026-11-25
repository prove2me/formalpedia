-- Prove2me | Theorems.Thm_GlobalTheory_canonGauge_dmonOf_hL_integral
-- name    : GlobalTheory.canonGauge_dmonOf_hL_integral
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:39:47.201224+00:00
-- url     : https://prove2.me/theorems/6fadff51-8fa8-4fdb-97cd-04a0a2fd98b4
-- title:
--   Global Theory: canon Gauge dmon Of h L integral
-- statement:
--   The Global Theory construction uses the canon Gauge dmon Of h L integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/CanonGaugeDmonOfHLIntegral.lean#L270-L357
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/CanonGaugeDmonOfHLIntegral.lean#L270-L357

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalSecondPointDerivativeSecondCoordinate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CanonGaugeDmonOfHLIntegral
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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open GlobalTheory.QuadDeriv
open GlobalTheory
open GaugeInt

theorem GlobalTheory.canonGauge_dmonOf_hL_integral :
    ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k]
      [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h : PS k 2 d), B.IsCanonGauge k h →
      ∀ (w0 : O) (ι : Type) [Fintype ι] (u : ι → Fin d → R),
      (∀ l l', dotProduct (fun i => algebraMap R k (u l i)) ((bilinPart k h).mulVec
        ((dAct k B w0).mulVec (fun i => algebraMap R k (u l' i)))) ∈ (algebraMap R k).range) →
      ∀ m : ι →₀ ℕ, constantCoeff (DmonOf (B.FK k) (fun l i => algebraMap R k (u l i)) m
        (B.hL k h w0)) ∈ (algebraMap R k).range := by sorry
