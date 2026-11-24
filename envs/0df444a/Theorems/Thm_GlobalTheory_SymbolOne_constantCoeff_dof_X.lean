-- Prove2me | Theorems.Thm_GlobalTheory_SymbolOne_constantCoeff_dof_X
-- name    : GlobalTheory.SymbolOne.constantCoeff_dof_X
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T20:24:32.888809+00:00
-- url     : https://prove2.me/theorems/4724dc58-415a-4b07-a5a7-eb8595e30361
-- title:
--   Symbol One: constant Coeff dof X
-- statement:
--   The Symbol One construction uses the constant Coeff dof X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ConstantCoeffDmonOfProdLinear.lean#L220-L237
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ConstantCoeffDmonOfProdLinear.lean#L220-L237

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofDApply
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeBilinearTermEqNegDoubleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_DerivationMemPowOfMemPowSucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ConstantCoeffDmonOfProdLinear
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
open GlobalTheory GlobalTheory.SymbolOne

theorem GlobalTheory.SymbolOne.constantCoeff_dof_X {R k : Type} [CommRing R] [CommRing k] (φ : R →+* k) {d : ℕ}
    (G : FGLaw R d) (v : Fin d → k) (j : Fin d) :
    constantCoeff (Dof (G.mapF φ) v (X ((0 : Fin 1), j))) = v j := by sorry
