-- Prove2me | Theorems.Thm_GlobalTheory_ColumnValue_column_value
-- name    : GlobalTheory.ColumnValue.column_value
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:53:14.574764+00:00
-- url     : https://prove2.me/theorems/ba88682c-77c5-42a5-93fc-da2c82c5a396
-- title:
--   Column Value: column value
-- statement:
--   The Column Value construction uses the column value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/NabValColumnsCongr.lean#L34-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/NabValColumnsCongr.lean#L34-L84

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
open GlobalTheory GlobalTheory.ColumnValue

theorem GlobalTheory.ColumnValue.column_value {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O] {k : Type}
    [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h : PS k 2 d) (hh : B.IsCanonGauge k h)
    (w0 a : O) (N m : ℕ) (w : PS R 1 d)
    (hw : FB.toK k w = FB.expS k (ev (n := 1) ![B.actK k a] (B.hL k h w0) - (N : k) • B.hL k h w0))
    (I : Ideal R) {ι : Type} [Fintype ι] (u : ι → Fin d → R) (α : ι → R) (hI : ∀ l, α l ∈ I)
    (hα : ∀ l, (dAct k B a).mulVec (fun i => algebraMap R k (u l i)) =
      algebraMap R k (α l) • (fun i => algebraMap R k (u l i)))
    (hβ : ∀ l l', dotProduct (fun i => algebraMap R k (u l i)) ((bilinPart k h).mulVec
      ((dAct k B w0).mulVec (fun i => algebraMap R k (u l' i)))) ∈ (algebraMap R k).range)
    (f : PS R 1 d) (y : ι → R) (hf : ∀ l mo, coeff mo (Dof B.G.F (u l) f - C (y l) * f) ∈ I)
    (mo : ι →₀ ℕ) :
    ∃ s : R, s - (∏ l, y l ^ mo l) * constantCoeff f ∈ I ∧
      B.nabVal k h w0 (N * m) (FB.toK k (f * w ^ m)) (fun l i => algebraMap R k (u l i))
        (MvPolynomial.monomial mo 1) = algebraMap R k s := by sorry
