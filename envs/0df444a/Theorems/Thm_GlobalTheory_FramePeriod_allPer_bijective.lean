-- Prove2me | Theorems.Thm_GlobalTheory_FramePeriod_allPer_bijective
-- name    : GlobalTheory.FramePeriod.allPer_bijective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:36:37.262203+00:00
-- url     : https://prove2.me/theorems/2d7cfd13-0fe7-4e35-9715-e16525384d51
-- title:
--   Frame Period: all Per bijective
-- statement:
--   The Frame Period construction uses the all Per bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/HermFormConjDiag.lean#L335-L347
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/HermFormConjDiag.lean#L335-L347

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ProdCastLESucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_EqTopOfForallEmbAllMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HermFormConjDiag
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors ComplexConjugate
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.FramePeriod
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem GlobalTheory.FramePeriod.allPer_bijective {Ψ : Finset (E →+* ℂ)} (Gm : Matrix (Fin r) (Fin r) E) (q : ℕ)
    (x : FD.Frame Ψ r) {g : ℕ} (idx : Fin g ≃ Ψ × Fin r)
    (h : ∀ τ : Ψ, Function.Bijective (locPer τ.1 Gm q (FD.mat x τ))) :
    Function.Bijective (allPer Gm q x idx) := by sorry
