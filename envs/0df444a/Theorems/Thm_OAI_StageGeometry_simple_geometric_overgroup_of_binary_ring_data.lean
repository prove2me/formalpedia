-- Prove2me | Theorems.Thm_OAI_StageGeometry_simple_geometric_overgroup_of_binary_ring_data
-- name    : OAI.StageGeometry.simple_geometric_overgroup_of_binary_ring_data
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T02:51:38.913304+00:00
-- url     : https://prove2.me/theorems/1bedba8e-3960-43d0-8bdc-953cb3fe7f55
-- title:
--   OAI.StageGeometry.simple_geometric_overgroup_of_binary_ring_data: intermediate lemma from OpenAI, Simple F-infinity overgroups of groups with decidable word problem (OpenAI result)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SimpleFInftyOvergroups.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Simple F-infinity overgroups of groups with decidable word problem (OpenAI result)*, OpenAI Math Release, September 23, 2026, result family 250, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.StageGeometry.simple_geometric_overgroup_of_binary_ring_data` of [lean/OAI/GroupTheory/FiniteType/StageGeometry.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/FiniteType/StageGeometry.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.StageGeometry`, with `open StageConstruction`):
--
--   ```lean
--   theorem simple_geometric_overgroup_of_binary_ring_data
--       (A : Type) [Finite A] (π : FreeAlgebra (ZMod 2) A →+* R)
--       (hπ : Function.Surjective π) (rel : Set (FreeAlgebra (ZMod 2) A))
--       (hrel : rel.Finite) (hker : TwoSidedIdeal.ker π=TwoSidedIdeal.span rel)
--       (g : G →* Rˣ) (hg : Function.Injective g) :
--       ∃ (H : Type) (_ : Group H), Nontrivial H ∧ IsSimpleGroup H ∧
--         SimpleFInftyOvergroups.HasTypeFInfty H ∧
--           ∃ ν : G →* H, Function.Injective ν
--   ```
--
--   **Definitions.** The statement is written with `OAI.CompressedSplittings.BinaryData` (definitions bundle `OAIQ66So003` of this split); `OAI.StageConstruction.Seven` (definitions bundle `OAIQ66So008` of this split); `OAI.StageConstruction.X` (definitions bundle `OAIQ66So015` of this split); `OAI.StageGeometry.PairDiagrams` (definitions bundle `OAIQ66So021` of this split); `OAI.StageConstruction.Q` and `OAI.StageConstruction.columnMulAction` (definitions bundle `OAIQ66So030` of this split); `OAI.SimpleFInftyOvergroups.HasTypeFInfty` (the published bundle `Def_SimpleOvergroups`).
--
--   **Used by.** The proof of `OAI.StageGeometry.simple_geometric_overgroup_of_corner_ring_data` of this split imports it.
-- source:
--   OpenAI, Simple F-infinity overgroups of groups with decidable word problem (OpenAI result), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 250; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/ComparatorChallenges/SimpleOvergroups.lean; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/FiniteType/StageGeometry.lean (declaration OAI.StageGeometry.simple_geometric_overgroup_of_binary_ring_data)

import Mathlib
import Definitions.Def_SimpleOvergroups
import Definitions.Def_OAIQ66So030

section

attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace StageGeometry
open StageConstruction
variable {R Y W G : Type} [Ring R] [Nontrivial R] [Group W] [MulAction W Y]
  [DecidableEq Y] [Group G]
variable (φ : R →ₙ+* R) (D : CompressedSplittings.BinaryData φ)
variable (e : R) (S T : Y → R)
variable (hTS : ∀ y y', T y*S y'=if y=y' then e else 0) (hSe : ∀ y, S y*e=S y)
variable (ρ : W →* Rˣ) (ι : Q R →* W) (point : X R → Y)
variable (hρS : ∀ w y, (ρ w).val*S y=S (w • y))
variable (hTρ : ∀ w y, T y*(ρ w).val=T (w⁻¹ • y))
variable (hpoint : ∀ q x, ι q • point x=point (q • x))
variable (hφ : Function.Injective φ) (hρ : Function.Injective ρ)
variable (hι : Function.Injective ι) (hpt : Function.Injective point) (he : e≠0)
variable (F₂ : PairDiagrams (ZMod 2) ι point) (F₃ : PairDiagrams (ZMod 3) ι point)

include φ D e S T ρ ι point hρS hTρ hpoint hφ hρ hι hpt he hTS hSe F₂ F₃ in

theorem simple_geometric_overgroup_of_binary_ring_data
    (A : Type) [Finite A] (π : FreeAlgebra (ZMod 2) A →+* R)
    (hπ : Function.Surjective π) (rel : Set (FreeAlgebra (ZMod 2) A))
    (hrel : rel.Finite) (hker : TwoSidedIdeal.ker π=TwoSidedIdeal.span rel)
    (g : G →* Rˣ) (hg : Function.Injective g) :
    ∃ (H : Type) (_ : Group H), Nontrivial H ∧ IsSimpleGroup H ∧
      SimpleFInftyOvergroups.HasTypeFInfty H ∧
        ∃ ν : G →* H, Function.Injective ν := by
  sorry
end StageGeometry

end
end

end OAI
end
