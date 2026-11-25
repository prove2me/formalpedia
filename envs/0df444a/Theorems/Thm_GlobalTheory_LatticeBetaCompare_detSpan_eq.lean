-- Prove2me | Theorems.Thm_GlobalTheory_LatticeBetaCompare_detSpan_eq
-- name    : GlobalTheory.LatticeBetaCompare.detSpan_eq
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T17:41:23.466705+00:00
-- url     : https://prove2.me/theorems/4510adae-92a5-4d5d-ab3f-d3f3acf51ef2
-- title:
--   Lattice Beta Compare: det Span eq
-- statement:
--   The Lattice Beta Compare construction uses the det Span eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/MultAddMultConjugate.lean#L124-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/MultAddMultConjugate.lean#L124-L126

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
variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem GlobalTheory.LatticeBetaCompare.detSpan_eq {L' L : Submodule (𝓞 E) (Fin n → E)} (hle : L ≤ L') (hfg : L'.FG)
    (hsp : Submodule.span E (L' : Set (Fin n → E)) = ⊤) : detSpan L = indexIdeal L' L • detSpan L' := by sorry
