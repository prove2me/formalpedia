-- Prove2me | Theorems.Thm_GlobalTheory_SerreTorsion_one_add_smul_pow_expand
-- name    : GlobalTheory.SerreTorsion.one_add_smul_pow_expand
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:46:01.164078+00:00
-- url     : https://prove2.me/theorems/9dc7d74e-9a89-4faa-bc2b-e2813c16d19c
-- title:
--   Serre Torsion: one add smul pow expand
-- statement:
--   The Serre Torsion construction uses the one add smul pow expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/EqOneOfPowEqOneOfCongrOne.lean#L27-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/EqOneOfPowEqOneOfCongrOne.lean#L27-L32

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_EqOneOfPowEqOneOfCongrOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.SerreTorsion
variable {E : Type} [Ring E]

theorem GlobalTheory.SerreTorsion.one_add_smul_pow_expand (c : ℕ) (ψ : E) (n : ℕ) :
    ∃ z : E, (1 + c • ψ) ^ n = 1 + c • (n • ψ + (n.choose 2 * c) • ψ ^ 2 + (c ^ 2) • z) := by sorry
