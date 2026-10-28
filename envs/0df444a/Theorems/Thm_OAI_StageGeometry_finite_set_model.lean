-- Prove2me | Theorems.Thm_OAI_StageGeometry_finite_set_model
-- name    : OAI.StageGeometry.finite_set_model
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T02:59:56.042684+00:00
-- url     : https://prove2.me/theorems/2cc4e235-80a7-400d-908b-8ffbbf794be4
-- title:
--   OAI.StageGeometry.finite_set_model: intermediate lemma from OpenAI, Simple F-infinity overgroups of groups with decidable word problem (OpenAI result)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SimpleFInftyOvergroups.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Simple F-infinity overgroups of groups with decidable word problem (OpenAI result)*, OpenAI Math Release, September 23, 2026, result family 250, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.StageGeometry.finite_set_model` of [lean/OAI/GroupTheory/FiniteType/HomStabilizer.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/FiniteType/HomStabilizer.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.StageGeometry`, with `open scoped Pointwise`, `open StageConstruction`):
--
--   ```lean
--   theorem finite_set_model [Group.IsFinitelyPresented (Steinberg.Group (Fin 6) R)]
--       (s : Set (LimitPoints φ S point)) (hs : s.Finite) :
--       letI := limitAction φ D S ρ ι point hρS hpoint hφ hρ hι
--       Nonempty (SimpleFInftyOvergroups.SplittingTorusModel
--         (fixingSubgroup (LimitGroup φ D ρ ι hφ hρ hι) s))
--   ```
--
--   **Definitions.** The statement is written with `OAI.AscendingHNN.associatedEquiv` (definitions bundle `OAIQ66So000` of this split); `OAI.CompressedSplittings.BinaryData`, `OAI.Steinberg.Group`, `OAI.Steinberg.Root` and `OAI.Steinberg.relations` (definitions bundle `OAIQ66So003` of this split); `OAI.StageConstruction.Seven` (definitions bundle `OAIQ66So008` of this split); `OAI.StageConstruction.X` (definitions bundle `OAIQ66So015` of this split); `OAI.StageGeometry.PairDiagrams` (definitions bundle `OAIQ66So021` of this split); `OAI.SimpleFInftyOvergroups.SplittingTorusModel` (definitions bundle `OAIQ66So026` of this split); `OAI.StageConstruction.Q` and `OAI.StageConstruction.columnMulAction` (definitions bundle `OAIQ66So030` of this split); `OAI.StageConstruction.LimitGroup`, `OAI.StageConstruction.LimitPoints`, `OAI.StageConstruction.delta` and `OAI.StageConstruction.delta_injective` (definitions bundle `OAIQ66So033` of this split); `OAI.StageGeometry.limitAction` (definitions bundle `OAIQ66So034` of this split).
--
--   **Used by.** The proof of `OAI.StageGeometry.localGroup_geometric_of_binary_ring_data` of this split imports it.
-- source:
--   OpenAI, Simple F-infinity overgroups of groups with decidable word problem (OpenAI result), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 250; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/ComparatorChallenges/SimpleOvergroups.lean; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/FiniteType/HomStabilizer.lean (declaration OAI.StageGeometry.finite_set_model)

import Mathlib
import Definitions.Def_OAIQ66So034

section

attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Pointwise
namespace SimpleFInftyOvergroups

attribute [instance] SplittingTorusModel.groupU SplittingTorusModel.groupP
  SplittingTorusModel.finitePresentation

end SimpleFInftyOvergroups

namespace StageGeometry
open StageConstruction
variable {R Y W : Type} [Ring R] [Nontrivial R] [Group W] [MulAction W Y] [DecidableEq Y]
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

include hTS hSe hTρ hpt he F₂ F₃ in
theorem finite_set_model [Group.IsFinitelyPresented (Steinberg.Group (Fin 6) R)]
    (s : Set (LimitPoints φ S point)) (hs : s.Finite) :
    letI := limitAction φ D S ρ ι point hρS hpoint hφ hρ hι
    Nonempty (SimpleFInftyOvergroups.SplittingTorusModel
      (fixingSubgroup (LimitGroup φ D ρ ι hφ hρ hι) s)) := by
  sorry

end StageGeometry

end

end OAI
end
