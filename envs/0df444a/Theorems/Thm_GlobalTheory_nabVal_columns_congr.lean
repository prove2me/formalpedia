-- Prove2me | Theorems.Thm_GlobalTheory_nabVal_columns_congr
-- name    : GlobalTheory.nabVal_columns_congr
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T00:56:17.370441+00:00
-- url     : https://prove2.me/theorems/e8af6bf5-bcbd-4cd0-9eb8-2a0ff0b0e522
-- title:
--   Global Theory: nab Val columns congr
-- statement:
--   The Global Theory construction uses the nab Val columns congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/NabValColumnsCongr.lean#L92-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/NabValColumnsCongr.lean#L92-L106

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_NabTrans
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_InvariantDerivAlongEndo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CanonGaugeDmonOfHLIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsGroupedOfSublist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ConstantCoeffDmonOfSubMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_NabValPullbackMonomial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_NabValColumnsCongr
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
open ColumnValue

theorem GlobalTheory.nabVal_columns_congr : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h : PS k 2 d), B.IsCanonGauge k h → ∀ (w0 a : O) (N m : ℕ) (w : PS R 1 d), FB.toK k w = FB.expS k (ev (n := 1) ![B.actK k a] (B.hL k h w0) - (N : k) • B.hL k h w0) → ∀ (I : Ideal R) (ι : Type) [Fintype ι] (u : ι → Fin d → R) (α : ι → R), (∀ l, α l ∈ I) → (∀ l, (dAct k B a).mulVec (fun i => algebraMap R k (u l i)) = algebraMap R k (α l) • (fun i => algebraMap R k (u l i))) → (∀ l l', dotProduct (fun i => algebraMap R k (u l i)) ((bilinPart k h).mulVec ((dAct k B w0).mulVec (fun i => algebraMap R k (u l' i)))) ∈ (algebraMap R k).range) → ∀ (n : ℕ) (f : Fin n → PS R 1 d) (y : ι × Fin n → R), (∀ l b mo, coeff mo (Dof B.G.F (u l) (f b) - C (y (l, b)) * f b) ∈ I) → ∀ P : MvPolynomial (ι × Fin n) R, ∃ r ∈ I, ∑ mo ∈ P.support, algebraMap R k (P.coeff mo) * ∏ b, B.nabVal k h w0 (N * m) (FB.toK k (f b * w ^ m)) (fun l i => algebraMap R k (u l i)) (MvPolynomial.monomial (colM mo b) 1) = algebraMap R k (MvPolynomial.eval y P * ∏ b, constantCoeff (f b) + r) := by sorry
