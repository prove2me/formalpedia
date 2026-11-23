-- Prove2me | Theorems.Thm_GlobalTheory_CMTransference_discr_smul_mem
-- name    : GlobalTheory.CMTransference.discr_smul_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:26:39.729393+00:00
-- url     : https://prove2.me/theorems/fd1ff07f-d31f-4e6f-8783-935bd90cd2ce
-- title:
--   CMTransference: discr smul mem
-- statement:
--   The CMTransference construction uses the discr smul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/CmApproximationTransference.lean#L206-L217
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/CmApproximationTransference.lean#L206-L217

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
variable {K : Type} [Field K] [NumberField K] {r : ℕ}

theorem GlobalTheory.CMTransference.discr_smul_mem [IsCMField K] {S : HermForm K r} {L : Submodule (𝓞 K) (Fin r → K)}
    (hL : IsSelfDual S L) {z : Fin r → K} (hz : ∀ y ∈ L, ∃ k : ℤ, traceForm S z y = k) :
    (discr K : K) • z ∈ L := by sorry
