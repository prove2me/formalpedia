-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_PullbackTensor_restrict_compatibility
-- name    : OAI.MaximalSeshadri.PullbackTensor.restrict_compatibility
-- status  : Open
-- author  : @wurtle
-- created : 2026-11-04T15:17:34.558493+00:00
-- url     : https://prove2.me/theorems/b0e4f2ff-26c7-4ff5-92de-331cb78a9e3a
-- title:
--   Pullback of tensor products and restriction
-- statement:
--   For $f:X\to Y$, an open $U\subset Y$, and modules $M,N$ on $Y$, the comparison `PullbackTensor.hom` between $f^*(M\otimes N)$ and $f^*M\otimes f^*N$ is compatible with restriction to $U$: the two composites of `OpenBaseChange.leftSquare`, `moduleTensorRestrict` and `hom` agree.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with `Definitions` files of this development imported in place of the upstream modules; these are supporting code for the statement.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0); Lean declaration `OAI.MaximalSeshadri.PullbackTensor.restrict_compatibility`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Sheaves/PullbackTensorRestrict.lean#L48

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

namespace OAI

section

namespace MaximalSeshadri.PullbackTensor
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open MaximalSeshadri.Geometry MaximalSeshadri.TensorPure

variable {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens)

theorem restrict_compatibility (M N : Y.Modules) :
    (OpenBaseChange.leftSquare f U).hom.app (moduleTensor Y M N) ≫
      (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).map (hom f M N) ≫
      (moduleTensorRestrict (f ⁻¹ᵁ U) ((Scheme.Modules.pullback f).obj M)
        ((Scheme.Modules.pullback f).obj N)).hom =
    (Scheme.Modules.pullback (f ∣_ U)).map (moduleTensorRestrict U M N).hom ≫
      hom (f ∣_ U) (M.restrict U.ι) (N.restrict U.ι) ≫
      moduleTensorMap ((OpenBaseChange.leftSquare f U).hom.app M)
        ((OpenBaseChange.leftSquare f U).hom.app N) := by
  sorry

end
end MaximalSeshadri.PullbackTensor
end
end OAI
