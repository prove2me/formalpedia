-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SiegelND_Integ_Arch_HuaInt_det_one_add_sq_eq_prod_eigenvalues
-- name    : GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.det_one_add_sq_eq_prod_eigenvalues
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T12:13:24.673799+00:00
-- url     : https://prove2.me/theorems/64ba7e4a-2997-4675-bc0e-968e089a92d6
-- title:
--   Hua Int: det one add sq eq prod eigenvalues
-- statement:
--   The Hua Int construction uses the det one add sq eq prod eigenvalues property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/OneLeDetW.lean#L9-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/OneLeDetW.lean#L9-L38

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SecondCountableHermC
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContinuousBlkM
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_OneLeDetW
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Arch GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt

theorem GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.det_one_add_sq_eq_prod_eigenvalues (n : ℕ) (b : Matrix (Fin n) (Fin n) ℂ) (hb : b.IsHermitian) :
    Matrix.det (1 + b * b) = ((∏ i, (1 + hb.eigenvalues i ^ 2) : ℝ) : ℂ) := by sorry
