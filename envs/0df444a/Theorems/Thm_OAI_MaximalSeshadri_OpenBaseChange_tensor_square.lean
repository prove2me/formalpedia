-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_OpenBaseChange_tensor_square
-- name    : OAI.MaximalSeshadri.OpenBaseChange.tensor_square
-- status  : Open
-- author  : @wurtle
-- created : 2026-11-04T15:06:28.978254+00:00
-- url     : https://prove2.me/theorems/1d9190b0-c74d-4eea-aa8b-7a834cb6fc3f
-- title:
--   Pushforward of tensor products and restriction
-- statement:
--   For $f:X\to Y$, an open $U\subset Y$, and modules $M,N$ on $X$, the comparison `PushforwardTensor.hom` between $f_*M\otimes f_*N$ and $f_*(M\otimes N)$ is compatible with restriction to $U$ through `iso f U` and `moduleTensorRestrict`.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with `Definitions` files of this development imported in place of the upstream modules; these are supporting code for the statement.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0); Lean declaration `OAI.MaximalSeshadri.OpenBaseChange.tensor_square`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Sheaves/TensorOpenSquare.lean#L61

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

namespace OAI

section

namespace MaximalSeshadri.OpenBaseChange
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open MaximalSeshadri.Geometry MaximalSeshadri.TensorPure

variable {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens)

theorem tensor_square (M N : X.Modules) :
    (Scheme.Modules.restrictFunctor U.ι).map (PushforwardTensor.hom f M N) ≫
      (iso f U (moduleTensor X M N)).hom ≫
      (Scheme.Modules.pushforward (f ∣_ U)).map
        (moduleTensorRestrict (f ⁻¹ᵁ U) M N).hom =
    (moduleTensorRestrict U ((Scheme.Modules.pushforward f).obj M)
      ((Scheme.Modules.pushforward f).obj N)).hom ≫
      moduleTensorMap (iso f U M).hom (iso f U N).hom ≫
      PushforwardTensor.hom (f ∣_ U) (M.restrict (f ⁻¹ᵁ U).ι) (N.restrict (f ⁻¹ᵁ U).ι) := by
  sorry

end
end MaximalSeshadri.OpenBaseChange
end
end OAI
