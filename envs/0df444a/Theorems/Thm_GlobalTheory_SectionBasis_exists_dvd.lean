-- Prove2me | Theorems.Thm_GlobalTheory_SectionBasis_exists_dvd
-- name    : GlobalTheory.SectionBasis.exists_dvd
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T02:52:22.476171+00:00
-- url     : https://prove2.me/theorems/b1f76b6c-34bd-42d5-aa2a-e8f56052a96f
-- title:
--   Section Basis: exists dvd
-- statement:
--   The Section Basis construction uses the exists dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ExistsDvdOfAlgebraic.lean#L150-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ExistsDvdOfAlgebraic.lean#L150-L158

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_PolyImgSuccAbove
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsDvdOfAlgebraic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.SectionBasis
open MvPolynomial ReciprocityTheory.ChartRestriction.G.T0 GlobalTheory.GenericSection
open scoped TensorProduct
variable {K Ω K' : Type} [Field K] [Field Ω] [Algebra K Ω] [Field K'] [Algebra K K'] {D N : ℕ}

theorem GlobalTheory.SectionBasis.exists_dvd (j0 : Fin (N + 1)) (x : Fin N → Ω)
    [Algebra (FractionRing (MvPolynomial (TVar D N) K)) (OmS Ω D N)]
    [FiniteDimensional (FractionRing (MvPolynomial (TVar D N) K)) (OmS Ω D N)]
    (hL : ∀ q : MvPolynomial (TVar D N) K, algebraMap (FractionRing (MvPolynomial (TVar D N) K)) (OmS Ω D N) (algebraMap (MvPolynomial (TVar D N) K) _ q) = sHom j0 x q)
    (f : MvPolynomial (SVar D N) Ω) (hf : f ≠ 0) :
    ∃ q : MvPolynomial (TVar D N) K, q ≠ 0 ∧ f ∣ aeval (polyImg j0 x) q := by sorry
