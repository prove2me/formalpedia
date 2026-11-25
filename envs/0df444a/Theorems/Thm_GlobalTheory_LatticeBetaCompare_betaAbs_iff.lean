-- Prove2me | Theorems.Thm_GlobalTheory_LatticeBetaCompare_betaAbs_iff
-- name    : GlobalTheory.LatticeBetaCompare.betaAbs_iff
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T17:46:17.046626+00:00
-- url     : https://prove2.me/theorems/a501f96e-9e6d-5424-8460-eafae98e9df6
-- title:
--   Lattice Beta Compare: beta Abs iff
-- statement:
--   The Lattice Beta Compare construction uses the beta Abs iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/MultAddMultConjugate.lean#L241-L244
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/MultAddMultConjugate.lean#L241-L244

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

theorem GlobalTheory.LatticeBetaCompare.betaAbs_iff (Λ : Lat E n) (β : c.F) : BetaAbs (Dw := Dw) c (toGen Λ) β ↔
    ∀ s : c.F →+* ℂ, ‖s β‖ ^ 2 = (Ideal.absNorm (latIdeal Λ) : ℝ) ^ (Dw.p + Dw.q) := by sorry
