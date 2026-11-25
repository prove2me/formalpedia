-- Prove2me | Theorems.Thm_GlobalTheory_CharacterColumns_nabVal_congr_dir
-- name    : GlobalTheory.CharacterColumns.nabVal_congr_dir
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:57:24.583025+00:00
-- url     : https://prove2.me/theorems/2e5d7474-96ed-43cd-a6fe-6664164ef591
-- title:
--   Character Columns: nab Val congr dir
-- statement:
--   The Character Columns construction uses the nab Val congr dir property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ConstantCoeffDmonOfEigen.lean#L28-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ConstantCoeffDmonOfEigen.lean#L28-L36

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ConstantCoeffDmonOfSubMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_NabValColumnsCongr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ConstantCoeffDmonOfEigen
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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory GlobalTheory.CharacterColumns

theorem GlobalTheory.CharacterColumns.nabVal_congr_dir {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
    {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h : PS k 2 d) (w0 : O)
    (m : ℕ) (f : PS k 1 d) {ι : Type} [Fintype ι] (u u' : ι → Fin d → k) (mo : ι →₀ ℕ)
    (hu : ∀ l, mo l ≠ 0 → u l = u' l) :
    B.nabVal k h w0 m f u (MvPolynomial.monomial mo 1) =
      B.nabVal k h w0 m f u' (MvPolynomial.monomial mo 1) := by sorry
