-- Prove2me | Theorems.Thm_GlobalTheory_ThetaUnifCompare_chi_neg_of_sym
-- name    : GlobalTheory.ThetaUnifCompare.chi_neg_of_sym
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T21:08:01.74357+00:00
-- url     : https://prove2.me/theorems/9a71c499-c973-417a-9d66-b5872abc96e8
-- title:
--   Theta Unif Compare: chi neg of sym
-- statement:
--   The Theta Unif Compare construction uses the chi neg of sym property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ChiEqOneOrOfSym.lean#L18-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ChiEqOneOrOfSym.lean#L18-L54

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_HermitianTensorPowers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ConstOfNormPeriodic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ChiEqOneOrOfSym
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.ThetaUnifCompare
open GlobalTheory.FrameValue GlobalTheory.IndefiniteRowSideFullHecke.HermitianTensorPowers CubeValues SymmetricSemicharacter EigenNorm
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} {u : HolUnif A L g}
  {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ}

theorem GlobalTheory.ThetaUnifCompare.chi_neg_of_sym (hL : L.IsLB) (hs : Out.Sym A L) (h : u.IsAH Hm χ) (l : u.Λ) : χ (-l) = χ l := by sorry
