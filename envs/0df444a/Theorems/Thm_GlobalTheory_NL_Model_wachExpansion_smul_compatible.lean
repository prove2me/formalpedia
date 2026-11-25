-- Prove2me | Theorems.Thm_GlobalTheory_NL_Model_wachExpansion_smul_compatible
-- name    : GlobalTheory.NL.Model.wachExpansion_smul_compatible
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:14:31.098586+00:00
-- url     : https://prove2.me/theorems/ca1062f0-6a38-53da-bae0-1e34e68a03cc
-- title:
--   Model: wach Expansion smul compatible
-- statement:
--   The Model construction uses the wach Expansion smul compatible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/UnramifiedSubfieldLeCyclotomicExt.lean#L301-L315
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/UnramifiedSubfieldLeCyclotomicExt.lean#L301-L315

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_NotFullBot
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnramifiedSubfieldLeCyclotomicExt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.NL GlobalTheory.NL.Model
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.NL
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem GlobalTheory.NL.Model.wachExpansion_smul_compatible (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL)
    (e : ↥(W.N T) → ℤ → T.V ⊗[Qp] B) (hs : ∀ x, ∃ m : ℤ, ∀ k < m, e x k = 0)
    (he : ∀ x k, W.levN T i ζ x k = ιV PD (LL := LL) (V := T.V) (e x k))
    (a : LetA O n) (x : ↥(W.N T)) : e (a • x) = conv (W.lev i ζ a) (e x) := by sorry
