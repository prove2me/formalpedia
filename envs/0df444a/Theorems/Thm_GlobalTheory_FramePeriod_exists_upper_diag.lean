-- Prove2me | Theorems.Thm_GlobalTheory_FramePeriod_exists_upper_diag
-- name    : GlobalTheory.FramePeriod.exists_upper_diag
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T13:39:00.048176+00:00
-- url     : https://prove2.me/theorems/a877cf06-0c92-469d-b4a3-11d4d378402e
-- title:
--   Frame Period: exists upper diag
-- statement:
--   The Frame Period construction uses the exists upper diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/HermFormConjDiag.lean#L15-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/HermFormConjDiag.lean#L15-L67

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

theorem GlobalTheory.FramePeriod.exists_upper_diag {n : ℕ} (q : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian)
    (hm : ∀ i : Fin (n + 1), 0 < FD.psgn q i * (FD.lminor A i).re) :
    ∃ (U : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℝ), U.BlockTriangular id ∧ U.det = 1 ∧
      Uᵀ * A * U.map (starRingEnd ℂ) = Matrix.diagonal (fun a => (d a : ℂ)) ∧
      ∀ a : Fin n, 0 < FD.sgn q a * d a := by sorry
