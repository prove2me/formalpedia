-- Prove2me | Theorems.Thm_GlobalTheory_LatticeBetaCompare_isBe_pow
-- name    : GlobalTheory.LatticeBetaCompare.isBe_pow
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T17:29:16.462909+00:00
-- url     : https://prove2.me/theorems/54b608d0-7ff7-41d5-95ba-dfc8c1b01f83
-- title:
--   Lattice Beta Compare: is Be pow
-- statement:
--   The Lattice Beta Compare construction uses the is Be pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/MultAddMultConjugate.lean#L395-L398
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/MultAddMultConjugate.lean#L395-L398

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
variable {Dw c}

theorem GlobalTheory.LatticeBetaCompare.isBe_pow {𝔞 : Ideal (𝓞 E)} {α : c.F} (h : IsBe Dw c 𝔞 α) (k : ℕ) : IsBe Dw c (𝔞 ^ k) (α ^ k) := by sorry
