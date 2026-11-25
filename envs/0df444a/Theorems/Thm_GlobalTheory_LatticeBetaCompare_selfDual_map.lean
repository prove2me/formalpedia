-- Prove2me | Theorems.Thm_GlobalTheory_LatticeBetaCompare_selfDual_map
-- name    : GlobalTheory.LatticeBetaCompare.selfDual_map
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T17:38:45.585815+00:00
-- url     : https://prove2.me/theorems/e7642a94-4fca-453c-b2a0-780db1288e68
-- title:
--   Lattice Beta Compare: self Dual map
-- statement:
--   The Lattice Beta Compare construction uses the self Dual map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/MultAddMultConjugate.lean#L490-L499
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/MultAddMultConjugate.lean#L490-L499

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
variable (Dw c)

theorem GlobalTheory.LatticeBetaCompare.selfDual_map {Λ : Lat E n} (h : Λ.SelfDual) {γ : (Fin n → E) ≃ₗ[E] (Fin n → E)} (hγ : IsUnitary γ) :
    (Λ.map γ).SelfDual := by sorry
