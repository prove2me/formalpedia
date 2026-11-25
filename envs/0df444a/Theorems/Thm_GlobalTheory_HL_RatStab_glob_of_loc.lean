-- Prove2me | Theorems.Thm_GlobalTheory_HL_RatStab_glob_of_loc
-- name    : GlobalTheory.HL.RatStab.glob_of_loc
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:24:21.823502+00:00
-- url     : https://prove2.me/theorems/05380b49-8979-406c-9bab-dc9a398caf4e
-- title:
--   Rat Stab: glob of loc
-- statement:
--   The Rat Stab construction uses the glob of loc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianStabiliserRationalUnitriangularPairs.lean#L158-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianStabiliserRationalUnitriangularPairs.lean#L158-L170

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramesCommonStabiliserEqPairingMatrixStabiliser
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RationalExtend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianStabiliserRationalUnitriangularPairs
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
noncomputable section
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.RatStab
open GlobalTheory.HL.FrameStab
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {A : Places F E sig} {r k : ℕ} (G : GFrames A r k) (p : HeightOneSpectrum (𝓞 F))

theorem GlobalTheory.HL.RatStab.glob_of_loc (u : Fin (r + 1) → Fin (k + 2 * r + 1) → (A.loc p).Ep) (v : Fin (r + 1) → G.V)
    (hu : ∀ a, u a = sc G p a • A.bc p (v a)) (s : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (h' : (Fin (k + 2 * r + 1) → (A.loc p).Ep) ≃ₗ[(A.loc p).Ep] (Fin (k + 2 * r + 1) → (A.loc p).Ep))
    (hl : ∀ j, h' (u j) = ∑ i, locM G p s i j • u i) (j : Fin (r + 1)) :
    h' (A.bc p (v j)) = A.bc p (∑ i, s i j • v i) := by sorry
