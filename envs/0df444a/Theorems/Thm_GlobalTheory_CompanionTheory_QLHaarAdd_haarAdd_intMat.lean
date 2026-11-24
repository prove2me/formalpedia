-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_QLHaarAdd_haarAdd_intMat
-- name    : GlobalTheory.CompanionTheory.QLHaarAdd.haarAdd_intMat
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T11:56:24.441664+00:00
-- url     : https://prove2.me/theorems/7991917b-5fc4-45be-89cc-e6517ba7ba55
-- title:
--   QLHaar Add: haar Add int Mat
-- statement:
--   The QLHaar Add construction uses the haar Add int Mat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/MatrixAdditiveHaarNormalized.lean#L38-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/MatrixAdditiveHaarNormalized.lean#L38-L69

import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldTopologyNormBallsStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MatrixAdditiveHaarNormalized
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QLHaarAdd

theorem GlobalTheory.CompanionTheory.QLHaarAdd.haarAdd_intMat : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}, LF O ϖ nrm q → ∀ n m : ℕ, BorelSpace (Matrix (Fin n) (Fin m) F) ∧ IsOpen (intMat O n m) ∧ IsCompact (intMat O n m) ∧ (∃ dx : Measure (Matrix (Fin n) (Fin m) F), dx.IsAddLeftInvariant ∧ dx (intMat O n m) = 1) ∧ (∀ (dx : Measure (Matrix (Fin n) (Fin m) F)), dx.IsAddLeftInvariant → dx (intMat O n m) = 1 → dx.IsAddHaarMeasure) ∧ (∀ (dx : Measure (Matrix (Fin n) (Fin m) F)), dx.IsAddLeftInvariant → dx (intMat O n m) = 1 → ∀ (dy : Measure (Matrix (Fin n) (Fin m) F)), dy.IsAddLeftInvariant → dy (intMat O n m) = 1 → dx = dy) := by sorry
