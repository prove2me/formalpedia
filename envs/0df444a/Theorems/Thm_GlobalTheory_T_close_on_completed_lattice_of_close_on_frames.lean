-- Prove2me | Theorems.Thm_GlobalTheory_T_close_on_completed_lattice_of_close_on_frames
-- name    : GlobalTheory.T.close_on_completed_lattice_of_close_on_frames
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:30:10.78559+00:00
-- url     : https://prove2.me/theorems/1f55924d-3dbd-4199-b7de-348fff6c5d05
-- title:
--   T: close on completed lattice of close on frames
-- statement:
--   The T construction uses the close on completed lattice of close on frames property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CloseOnCompletedLatticeOfCloseOnFramesStatement.lean#L17-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CloseOnCompletedLatticeOfCloseOnFramesStatement.lean#L17-L18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CloseOnCompletedLatticeOfCloseOnFrames
import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramesCommonStabiliserEqPairingMatrixStabiliser
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RationalExtend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsIntegralOfQuad
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CloseOnCompletedLatticeOfCloseOnFramesStatement
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

theorem GlobalTheory.T.close_on_completed_lattice_of_close_on_frames : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig) (r k : ℕ) (G : GFrames A r k) (Λ : G.Lt) (D : ℤ) (p : HeightOneSpectrum (𝓞 F)) (h : (G.S p).GLV) (M M' : Matrix (Fin (r + 1)) (Fin (r + 1)) (A.loc p).Ep) (t : (A.loc p).Fp), (Matrix.of fun k l : Fin (r + 1) ⊕ Fin (r + 1) => ∑ i, ∑ j, Sum.elim G.f G.f' k i * G.Hm i j * sig (Sum.elim G.f G.f' l j))⁻¹ * (Matrix.of fun k l : Fin (r + 1) ⊕ Fin (r + 1) => ∑ i, ∑ j, Sum.elim G.f G.f' k i * G.Hm i j * sig (Sum.elim G.f G.f' l j)) = 1 → (∀ k l, ∃ o : 𝓞 E, (D : E) * (Matrix.of fun k l : Fin (r + 1) ⊕ Fin (r + 1) => ∑ i, ∑ j, Sum.elim G.f G.f' k i * G.Hm i j * sig (Sum.elim G.f G.f' l j))⁻¹ k l = o) → (∀ x ∈ Λ, ∀ l, ∃ o : 𝓞 E, (D : E) * ∑ a, ∑ b, x a * G.Hm a b * sig (Sum.elim G.f G.f' l b) = o) → (∀ l, (D : 𝓞 E) • Sum.elim G.f G.f' l ∈ Λ) → h ∈ (G.S p).St → (∀ j, h (A.bc p (G.f j)) = ∑ i, M i j • A.bc p (G.f i)) → (∀ j, h (A.bc p (G.f' j)) = ∑ i, M' i j • A.bc p (G.f' i)) → (∀ i j, ∃ o ∈ (A.L p).O, (M - 1) i j = algebraMap (A.loc p).Fp (A.loc p).Ep (t * (D : (A.loc p).Fp) ^ 3) * o) → (∀ i j, ∃ o ∈ (A.L p).O, (M' - 1) i j = algebraMap (A.loc p).Fp (A.loc p).Ep (t * (D : (A.loc p).Fp) ^ 3) * o) → ∀ x ∈ A.lat p Λ, ∃ y ∈ A.lat p Λ, h x - x = algebraMap (A.loc p).Fp (A.loc p).Ep t • y := by sorry
