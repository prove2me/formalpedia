-- Prove2me | Theorems.Thm_GlobalTheory_ResidueCharacterDense_prod_psi
-- name    : GlobalTheory.ResidueCharacterDense.prod_psi
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:29:45.003332+00:00
-- url     : https://prove2.me/theorems/920539e3-007e-5f7e-9f67-e407fc02b7f8
-- title:
--   Residue Character Dense: prod psi
-- statement:
--   The Residue Character Dense construction uses the prod psi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/T2SpaceIsNonarchimedeanLocalFieldSingleBlock.lean#L379-L456
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/T2SpaceIsNonarchimedeanLocalFieldSingleBlock.lean#L379-L456

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_T2SpaceIsNonarchimedeanLocalFieldSingleBlock
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel IsDedekindDomain NumberField Filter Topology
open scoped TensorProduct
open GlobalTheory GlobalTheory.ResidueCharacterDense
open Formalism.MainNotions.S.Loc

theorem GlobalTheory.ResidueCharacterDense.prod_psi {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (hE : Module.finrank F E = 2) {sig : E →ₐ[F] E}
    (A : (p : HeightOneSpectrum (𝓞 F)) → LocAt F E sig p) {l : ℕ} (hl : l.Prime) (y : E)
    (hy : IsIntegral ℤ y) (k : ℕ) :
    Set.Finite (Function.mulSupport fun p : HeightOneSpectrum (𝓞 F) =>
      (A p).psiE ((A p).ιE (y / (l : E) ^ k))) ∧
    ∏ᶠ p : HeightOneSpectrum (𝓞 F), (A p).psiE ((A p).ιE (y / (l : E) ^ k)) =
      Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ E (y / (l : E) ^ k) : ℚ) : ℂ)) := by sorry
