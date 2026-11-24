-- Prove2me | Theorems.Thm_GlobalTheory_HermSign_exists_diag_of_complexStructure
-- name    : GlobalTheory.HermSign.exists_diag_of_complexStructure
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T14:19:30.189667+00:00
-- url     : https://prove2.me/theorems/d13cb5bb-785e-4e11-9deb-68c276955a96
-- title:
--   Herm Sign: exists diag of complex Structure
-- statement:
--   The Herm Sign construction uses the exists diag of complex Structure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/SignatureHermitianModelOfDatum.lean#L111-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/SignatureHermitianModelOfDatum.lean#L111-L161

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_MemIffConjugateNotMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_SignatureHermitianModelOfDatum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors TensorProduct ComplexConjugate ComplexOrder MatrixOrder
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HermSign

theorem GlobalTheory.HermSign.exists_diag_of_complexStructure {r m n : ℕ} (hr : r = m + n)
    (G M : Matrix (Fin r) (Fin r) ℂ) (hG : G.IsHermitian) (s : ℝ) (ε : ℝ) (hε : ε * ε = 1)
    (hs : 0 < ε * s) (hM : M * M = -1)
    (hinv : ∀ u v : Fin r → ℂ, ((s * Complex.I) * ((M *ᵥ u) ⬝ᵥ G *ᵥ star (M *ᵥ v))).re =
      ((s * Complex.I) * (u ⬝ᵥ G *ᵥ star v)).re)
    (hpos : ∀ u : Fin r → ℂ, u ≠ 0 → 0 < ((s * Complex.I) * ((M *ᵥ u) ⬝ᵥ G *ᵥ star u)).re)
    (ht : ε * Complex.I * M.trace = (m : ℂ) - n) :
    ∃ N : Matrix (Fin r) (Fin r) ℂ, N.det ≠ 0 ∧
      Nᴴ * G * N = diagonal fun a : Fin r => ((FD.sgn m (a : ℕ) : ℝ) : ℂ) := by sorry
