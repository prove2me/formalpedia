-- Prove2me | Theorems.Thm_GlobalTheory_T_frameMatrix_close_gives_lattice_close_integral
-- name    : GlobalTheory.T.frameMatrix_close_gives_lattice_close_integral
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:55:48.556285+00:00
-- url     : https://prove2.me/theorems/e5142b25-d9df-5f0c-8908-125954aeb5dc
-- title:
--   T: frame Matrix close gives lattice close integral
-- statement:
--   The T construction uses the frame Matrix close gives lattice close integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/FrameMatrixCloseGivesLatticeCloseIntegralStatement.lean#L11-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/FrameMatrixCloseGivesLatticeCloseIntegralStatement.lean#L11-L12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FrameMatrixCloseGivesLatticeCloseIntegral
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FrameMatrixCloseGivesLatticeCloseIntegralStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.frameMatrix_close_gives_lattice_close_integral : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (r k : ℕ) (G : GFrames A r k), ∀ Λ : G.Lt, Submodule.IsLattice E Λ → ∃ d : ∀ p, (A.loc p).Fp, (∀ p, d p ≠ 0) ∧ {p | ¬ ∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = d p}.Finite ∧ ∀ p (c0 : (A.loc p).Fp) (h : (G.S p).GLV) (M : Matrix (Fin (r + 1)) (Fin (r + 1)) (A.loc p).Ep), c0 ≠ 0 → c0 ∈ 𝒪[(A.loc p).Fp] → h ∈ (G.S p).St → (∀ j, h (A.bc p (G.f j)) = ∑ i, M i j • A.bc p (G.f i)) → (∀ i j, ∃ o ∈ (A.L p).O, (M - 1) i j = algebraMap (A.loc p).Fp (A.loc p).Ep (c0 * d p) * o) → h ∈ (G.S p).K0 ∧ ∀ x ∈ A.lat p Λ, ∃ y ∈ A.lat p Λ, h x - x = algebraMap (A.loc p).Fp (A.loc p).Ep c0 • y := by sorry
