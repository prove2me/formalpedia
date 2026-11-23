-- Prove2me | Theorems.Thm_GlobalTheory_CongruenceIndex_exists_finset_cosets
-- name    : GlobalTheory.CongruenceIndex.exists_finset_cosets
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:51:29.214374+00:00
-- url     : https://prove2.me/theorems/bbf5733b-f3de-4cf3-a4c4-600628eddf00
-- title:
--   Congruence Index: exists finset cosets
-- statement:
--   The Congruence Index construction uses the exists finset cosets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/CongruenceFiniteIndex.lean#L141-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/CongruenceFiniteIndex.lean#L141-L182

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_CongruenceFiniteIndex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CongruenceIndex
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
  {Gm : Matrix (Fin r) (Fin r) E} {Λ : Submodule (𝓞 E) (Fin r → E)}
open NumberField Matrix
open scoped nonZeroDivisors
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
  {Gm : Matrix (Fin r) (Fin r) E} {Λ : Submodule (𝓞 E) (Fin r → E)}

theorem GlobalTheory.CongruenceIndex.exists_finset_cosets (hΛ : Λ.FG) {M : ℕ} (hM : 0 < M) :
    ∃ S : Finset (GL (Fin r) E), ∀ γ, _root_.ReciprocityTheory.ChartRestriction.G.FD.IsUStab Gm Λ γ →
      ∃ s ∈ S, s⁻¹ * γ ∈ _root_.GlobalTheory.CongruenceIndex.congruenceSubgroup Gm Λ M := by sorry
