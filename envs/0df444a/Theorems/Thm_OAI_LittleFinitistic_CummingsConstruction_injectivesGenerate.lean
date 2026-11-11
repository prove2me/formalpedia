-- Prove2me | Theorems.Thm_OAI_LittleFinitistic_CummingsConstruction_injectivesGenerate
-- name    : OAI.LittleFinitistic.CummingsConstruction.injectivesGenerate
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T15:26:41.491041+00:00
-- url     : https://prove2.me/theorems/8ff3d165-bc42-493e-8562-6732982451b9
-- title:
--   OAI.LittleFinitistic.CummingsConstruction.injectivesGenerate: intermediate lemma from OpenAI, An algebra of infinite little finitistic dimension (result family 198)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.LittleFinitistic.extreme_left_right_asymmetry`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An algebra of infinite little finitistic dimension (result family 198)*, OpenAI Math Release, September 23, 2026, result family 198, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.LittleFinitistic.CummingsConstruction.injectivesGenerate` of [lean/OAI/Algebra/FinitisticAsymmetry/Triangular/Generation.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/FinitisticAsymmetry/Triangular/Generation.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.LittleFinitistic.CummingsConstruction`, with `open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated HomologicalComplex`):
--
--   ```lean
--   lemma injectivesGenerate [Fintype ι] (hχ : Function.Surjective χ)
--       (hnil : ∃ n : ℕ, (RingHom.ker χ.toRingHom)^n = ⊥) :
--       InjectivesGenerate (T χ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.LittleFinitistic.CummingsConstruction.NewCorner`, `OAI.LittleFinitistic.CummingsConstruction.SimpleSum`, `OAI.LittleFinitistic.CummingsConstruction.T`, `OAI.LittleFinitistic.TriangularConstruction.OffDiagonal`, `OAI.LittleFinitistic.CummingsConstruction.SimpleSum.instAddCommGroup`, `OAI.LittleFinitistic.CummingsConstruction.SimpleSum.instModuleMulOpposite`, `OAI.LittleFinitistic.CummingsConstruction.SimpleSum.instModuleNewCorner`, `OAI.LittleFinitistic.CummingsConstruction.SimpleSum.instSMulCommClassNewCornerMulOpposite`, `OAI.LittleFinitistic.TriangularConstruction.OffDiagonal.instAddCommGroup`, `OAI.LittleFinitistic.TriangularConstruction.OffDiagonal.instModuleMulOppositeProd`, `OAI.LittleFinitistic.TriangularConstruction.OffDiagonal.instModuleProd` and `OAI.LittleFinitistic.TriangularConstruction.OffDiagonal.instSMulCommClassProdMulOpposite` (definitions bundle `Q221FA000` of this split); `OAI.LittleFinitistic.InjectivesGenerate` (the published bundle `Def_FinitisticAsymmetry`).
--
--   **Used by.** The proof of `OAI.LittleFinitistic.extreme_left_right_asymmetry` of this split imports it.
-- source:
--   OpenAI, An algebra of infinite little finitistic dimension (result family 198), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 198; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-algebra-of-infinite-little-finitistic-dimension-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/FinitisticAsymmetry/Triangular/Generation.lean (declaration OAI.LittleFinitistic.CummingsConstruction.injectivesGenerate)

import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.RingTheory.Finiteness.Defs
import Definitions.Def_FinitisticAsymmetry
import Definitions.Def_Q221FA000

section

attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated HomologicalComplex
namespace LittleFinitistic.CummingsConstruction
universe u w
variable {k C ι : Type u} [Field k] [Ring C] [Algebra k C]
variable (χ : C →ₐ[k] (ι → k)) (i : ι)

variable [HasDerivedCategory.{w} (ModuleCat.{u} (T χ))]

variable (P : ObjectProperty (DerivedCategory (ModuleCat.{u} (T χ))))
  [P.IsClosedUnderIsomorphisms] [P.IsTriangulated]
  [P.IsClosedUnderColimitsOfShape (Discrete ℕ)]
  (hI : ∀ M : ModuleCat.{u} (T χ), Injective M →
    P ((DerivedCategory.singleFunctor (ModuleCat (T χ)) 0).obj M))

include hI

omit hI [HasDerivedCategory.{w} (ModuleCat.{u} (T χ))] in
lemma injectivesGenerate [Fintype ι] (hχ : Function.Surjective χ)
    (hnil : ∃ n : ℕ, (RingHom.ker χ.toRingHom)^n = ⊥) :
    InjectivesGenerate (T χ) := by
  sorry

end LittleFinitistic.CummingsConstruction

end

end OAI
end
