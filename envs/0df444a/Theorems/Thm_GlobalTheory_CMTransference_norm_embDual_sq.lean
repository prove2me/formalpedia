-- Prove2me | Theorems.Thm_GlobalTheory_CMTransference_norm_embDual_sq
-- name    : GlobalTheory.CMTransference.norm_embDual_sq
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:05:13.078029+00:00
-- url     : https://prove2.me/theorems/2d278cd4-693d-44a6-830d-e7b107e27d42
-- title:
--   CMTransference: norm emb Dual sq
-- statement:
--   The CMTransference construction uses the norm emb Dual sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/CmApproximationTransference.lean#L253-L262
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/CmApproximationTransference.lean#L253-L262

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

theorem GlobalTheory.CMTransference.norm_embDual_sq (x : Fin r → K) : ‖embDual p σ Q x‖ ^ 2 = 4 * majSq σ Q x := by sorry
