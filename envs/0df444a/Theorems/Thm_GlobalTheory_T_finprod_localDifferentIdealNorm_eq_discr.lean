-- Prove2me | Theorems.Thm_GlobalTheory_T_finprod_localDifferentIdealNorm_eq_discr
-- name    : GlobalTheory.T.finprod_localDifferentIdealNorm_eq_discr
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:31:32.017871+00:00
-- url     : https://prove2.me/theorems/27790dad-a469-40f6-b583-1fb9e8c0b836
-- title:
--   T: finprod local Different Ideal Norm eq discr
-- statement:
--   The T construction uses the finprod local Different Ideal Norm eq discr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/FinprodLocalDifferentIdealNormEqDiscrStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/FinprodLocalDifferentIdealNormEqDiscrStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_FinprodLocalDifferentIdealNormEqDiscr
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_LocalDualIndex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_FinprodLocalDifferentIdealNormEqDiscrStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.finprod_localDifferentIdealNorm_eq_discr : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] (σ : E →ₐ[F] E), IsCMExt F E σ → (∀ x : E, star x = σ x) → Formalism.HermitianLatticesTheory.IsCMUnram E → (Function.mulSupport (normDifferentV F)).Finite ∧ ((∏ᶠ v, normDifferentV F v : ℕ) : ℝ) = absDiscr F ∧ absDiscr F = (2 * Formalism.HermitianLatticesTheory.vInv E) ^ Formalism.HermitianLatticesTheory.fDeg E := by sorry
