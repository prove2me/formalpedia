-- Prove2me | Theorems.Thm_GlobalTheory_exists_integral_germ_nabVal_congr
-- name    : GlobalTheory.exists_integral_germ_nabVal_congr
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:55:46.112266+00:00
-- url     : https://prove2.me/theorems/4e863ccc-9a5e-4af1-a1b8-626b05689122
-- title:
--   Global Theory: exists integral germ nab Val congr
-- statement:
--   The Global Theory construction uses the exists integral germ nab Val congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ExistsIntegralGermNabValCongr.lean#L39-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ExistsIntegralGermNabValCongr.lean#L39-L120

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_NabTrans
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_MapDofIterate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_InvariantDerivAlongEndo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsGroupedOfSublist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_PowerSeriesExpIntegralCanonGaugeAdditiveSecond
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_NabValPullbackMonomial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsIntegralGermNabValCongr
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
open GlobalTheory
open IntegralColumnGerm

theorem GlobalTheory.exists_integral_germ_nabVal_congr :
  (∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h : PS k 2 d), B.IsCanonGauge k h → ∀ (w : O) (N : ℕ) (ι : Type) [Fintype ι] (u : ι → Fin d → R),
    (∀ l l', dotProduct (fun i => algebraMap R k (u l i)) ((bilinPart k h).mulVec ((dAct k B w).mulVec (fun i => algebraMap R k (u l' i)))) ∈ (algebraMap R k).range) →
    ∀ mo : ι →₀ ℕ, ∃ r : R, constantCoeff (DmonOf (B.FK k) (fun l i => algebraMap R k (u l i)) mo (B.hL k h ((N : O) * w))) = algebraMap R k (N * r)) →
  (∀ (R : Type) [CommRing R] (d : ℕ) (F : Fin d → PS R 2 d) (I : Ideal R) (ι : Type) [Fintype ι] (u : ι → Fin d → R) (f f' g : PS R 1 d),
    (∀ mo : ι →₀ ℕ, constantCoeff (DmonOf F u mo f) - constantCoeff (DmonOf F u mo f') ∈ I) →
    ∀ mo : ι →₀ ℕ, constantCoeff (DmonOf F u mo (f * g)) - constantCoeff (DmonOf F u mo (f' * g)) ∈ I) →
  (∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h : PS k 2 d), B.IsCanonGauge k h → Function.Injective (algebraMap R k) → ∀ (w0 a c : O) (N m : ℕ) (I : Ideal R), star a * a = (N : O) * c → (N : R) ∈ I →
    ∀ (ι : Type) [Fintype ι] (u : ι → Fin d → R) (α : ι → R), (∀ l, α l - 1 ∈ I) → (∀ l, IsUnit (α l)) →
    (∀ l, (dAct k B a).mulVec (fun i => algebraMap R k (u l i)) = algebraMap R k (α l) • (fun i => algebraMap R k (u l i))) →
    (∀ l l', dotProduct (fun i => algebraMap R k (u l i)) ((bilinPart k h).mulVec ((dAct k B (c * w0)).mulVec (fun i => algebraMap R k (u l' i)))) ∈ (algebraMap R k).range) →
    ∀ χ : PS R 1 d, ∃ g : PS R 1 d, ∀ mo : ι →₀ ℕ, ∃ r ∈ I,
      B.nabVal k h w0 m (FB.toK k g) (fun l i => algebraMap R k (u l i)) (MvPolynomial.monomial mo 1) =
        algebraMap R k (constantCoeff (DmonOf B.G.F u mo χ) + r)) := by sorry
