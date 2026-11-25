-- Prove2me | Theorems.Thm_GlobalTheory_SectionBasis_sHom_eq
-- name    : GlobalTheory.SectionBasis.sHom_eq
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T01:29:57.547131+00:00
-- url     : https://prove2.me/theorems/699d4cdb-6498-4fcf-b609-7935818cd2c1
-- title:
--   Section Basis: s Hom eq
-- statement:
--   The Section Basis construction uses the s Hom eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ExistsDvdOfAlgebraic.lean#L95-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ExistsDvdOfAlgebraic.lean#L95-L104

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

theorem GlobalTheory.SectionBasis.sHom_eq (j0 : Fin (N + 1)) (x : Fin N → Ω) (q : MvPolynomial (TVar D N) K) :
    sHom j0 x q = algebraMap (MvPolynomial (SVar D N) Ω) (OmS Ω D N) (aeval (polyImg j0 x) q) := by sorry
