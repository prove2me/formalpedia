-- Prove2me | Theorems.Thm_GlobalTheory_FramePeriod_exists_loc
-- name    : GlobalTheory.FramePeriod.exists_loc
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:37:17.301994+00:00
-- url     : https://prove2.me/theorems/e8566bee-a2e6-4539-8b66-90476214a6b7
-- title:
--   Frame Period: exists loc
-- statement:
--   The Frame Period construction uses the exists loc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/HermFormConjDiag.lean#L101-L202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/HermFormConjDiag.lean#L101-L202

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

theorem GlobalTheory.FramePeriod.exists_loc (τ : E →+* ℂ) (Gm : Matrix (Fin r) (Fin r) E) (hG : ∀ a b, FD.cc (Gm a b) = Gm b a)
    (q : ℕ) (M : Matrix (Fin r) (Fin r) ℂ) (hM : M.det ≠ 0)
    (hm : ∀ i : Fin (r + 1), 0 < FD.psgn q i * (FD.lminor (FD.gram τ Gm M) i).re) :
    Function.Bijective (locPer τ Gm q M) ∧ ∃ Hl : Matrix (Fin r) (Fin r) ℂ, Hl.IsHermitian ∧
      (∀ z, z ≠ 0 → 0 < (hermForm Hl z z).re) ∧
      ∀ u w, (hermForm Hl (locPer τ Gm q M u) (locPer τ Gm q M w)).im = -(FD.hermC τ Gm u w).im := by sorry
