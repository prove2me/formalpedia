-- Prove2me | Theorems.Thm_GlobalTheory_CMTransference_normSq_le_majSq
-- name    : GlobalTheory.CMTransference.normSq_le_majSq
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:04:57.691953+00:00
-- url     : https://prove2.me/theorems/5fe8e079-f95c-45a4-b54c-06eec41cc65f
-- title:
--   CMTransference: norm Sq le maj Sq
-- statement:
--   The CMTransference construction uses the norm Sq le maj Sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/CmApproximationTransference.lean#L269-L272
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/CmApproximationTransference.lean#L269-L272

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CoveringRadiusStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_Transference
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_BabaiCovering
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ConjugateConjugate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_CmApproximationTransference
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CMTransference
open NumberField Matrix Module Submodule ReciprocityTheory.MultiplicativeHeights ComplexConjugate
variable {K : Type} [Field K] [NumberField K] {r : ℕ} {ι : Type} [Fintype ι]
variable (p : ℕ) (σ : ι → K →+* ℂ) (Q : ι → Matrix (Fin r) (Fin r) ℂ)

theorem GlobalTheory.CMTransference.normSq_le_majSq (i : ι) (x : Fin r → K) :
    normSq (Q i *ᵥ embVec (σ i) x) ≤ majSq σ Q x := by sorry
