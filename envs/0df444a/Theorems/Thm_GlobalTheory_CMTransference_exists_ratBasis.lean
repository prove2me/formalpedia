-- Prove2me | Theorems.Thm_GlobalTheory_CMTransference_exists_ratBasis
-- name    : GlobalTheory.CMTransference.exists_ratBasis
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T11:05:14.413546+00:00
-- url     : https://prove2.me/theorems/5e260ca2-6b0f-4502-b25c-30373d4b24a6
-- title:
--   CMTransference: exists rat Basis
-- statement:
--   The CMTransference construction uses the exists rat Basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/CmApproximationTransference.lean#L126-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/CmApproximationTransference.lean#L126-L175

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

theorem GlobalTheory.CMTransference.exists_ratBasis {L : Submodule (𝓞 K) (Fin r → K)} (hL : IsLattice L) :
    ∃ (n : ℕ) (b : Basis (Fin n) ℚ (Fin r → K)),
      ∀ x, x ∈ L ↔ x ∈ span ℤ (Set.range b) := by sorry
