-- Prove2me | Theorems.Thm_GlobalTheory_LatticeBetaCompare_isBe_iff
-- name    : GlobalTheory.LatticeBetaCompare.isBe_iff
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T17:30:13.318104+00:00
-- url     : https://prove2.me/theorems/da217d11-5045-56c8-95bb-64cc43307726
-- title:
--   Lattice Beta Compare: is Be iff
-- statement:
--   The Lattice Beta Compare construction uses the is Be iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/MultAddMultConjugate.lean#L262-L267
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/MultAddMultConjugate.lean#L262-L267

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_ReflexNormIndexIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsMulMemOfMemSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsCoeEqSpanDetOfIntVecLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_MultAddMultConjugate
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
open GlobalTheory GlobalTheory.LatticeBetaCompare
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice GlobalTheory.IndefiniteRowSideFullHecke.ReflexNormIndexIdeal GlobalTheory.GenusLatCompare
open scoped nonZeroDivisors Pointwise
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
variable {H : Host E} (Dw : Datum H) {l : Level H} (c : Coeff l)

theorem GlobalTheory.LatticeBetaCompare.isBe_iff (𝔞 : Ideal (𝓞 E)) (β : c.F) : IsBe Dw c 𝔞 β ↔
    Submodule.span (𝓞 c.F) {β} =
      ∏ τ : E →+* ℂ, Submodule.span (𝓞 c.F) ((embK c τ) '' (𝔞 : Set (𝓞 E))) ^ Dw.mult τ ∧
    ∀ σ : c.F →+* ℂ, ‖σ β‖ ^ 2 = (Ideal.absNorm 𝔞 : ℝ) ^ (Dw.p + Dw.q) := by sorry
