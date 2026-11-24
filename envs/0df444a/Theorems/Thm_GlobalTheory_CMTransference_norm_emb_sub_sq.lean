-- Prove2me | Theorems.Thm_GlobalTheory_CMTransference_norm_emb_sub_sq
-- name    : GlobalTheory.CMTransference.norm_emb_sub_sq
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T11:04:45.888629+00:00
-- url     : https://prove2.me/theorems/20350a26-3ecb-44f5-a2ca-4c8b88d371d1
-- title:
--   CMTransference: norm emb sub sq
-- statement:
--   The CMTransference construction uses the norm emb sub sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/CmApproximationTransference.lean#L243-L247
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/CmApproximationTransference.lean#L243-L247

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

theorem GlobalTheory.CMTransference.norm_emb_sub_sq (x : Fin r → K) (w : ι → Fin r → ℂ) :
    ‖(WithLp.toLp 2 fun ik : ι × Fin r => w ik.1 ik.2 : EuclideanSpace ℂ (ι × Fin r)) -
      emb σ Q x‖ ^ 2 = ∑ i, normSq (Q i *ᵥ embVec (σ i) x - w i) := by sorry
