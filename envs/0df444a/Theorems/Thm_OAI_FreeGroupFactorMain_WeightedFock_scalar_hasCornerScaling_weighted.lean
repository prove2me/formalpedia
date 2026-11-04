-- Prove2me | Theorems.Thm_OAI_FreeGroupFactorMain_WeightedFock_scalar_hasCornerScaling_weighted
-- name    : OAI.FreeGroupFactorMain.WeightedFock.scalar_hasCornerScaling_weighted
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T03:11:11.431006+00:00
-- url     : https://prove2.me/theorems/1f03640b-ce62-498e-bd71-0bc0147ca810
-- title:
--   Corner scaling of the scalar Gaussian algebra by a weight
-- statement:
--   Let $u,v$ be real with $0<v<u$ and $u^2+v^2=1$. Let $\mathcal N$ be the scalar Gaussian algebra with vacuum trace $\tau$ and its ultraweak topology. Then $\mathcal N$ has corner scaling at $u^2$: there are a projection $p\in\mathcal N$ with $\tau(p)=u^2$ and a $*$-isomorphism $e:\mathcal N\to p\mathcal Np$, ultraweakly bicontinuous, with
--
--   $$\tau(e(x))=u^2\tau(x).$$
--
--   This is the corner-scaling input for the amplification calculus.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with the listed `Definitions` imported in place of the upstream modules; the definitions are supporting code for this statement.
-- source:
--   OpenAI, An isomorphism of the free group factors, September 23, 2026, https://github.com/openai/math (paper: preprints/An-isomorphism-of-the-free-group-factors-September-23-2026/An-isomorphism-of-the-free-group-factors-September-23-2026.pdf; Lean: lean/OAI/Analysis/FreeGroupFactor and lean/OAI/Analysis/InterpolatedFactors, Apache License 2.0); Lean declaration `OAI.FreeGroupFactorMain.WeightedFock.scalar_hasCornerScaling_weighted`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/InterpolatedFactors/Scaling.lean#L124

import Mathlib
import Definitions.Def_FreeGroupFactorProof18

namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7

namespace FreeGroupFactorMain.Amplification

section
variable {A : Type u_1} {B : Type u_2} [CStarAlgebra A] [CStarAlgebra B]

end

variable {A : Type u_3} {B : Type u_4} [CStarAlgebra A] [CStarAlgebra B]

end FreeGroupFactorMain.Amplification

namespace FreeGroupFactorMain.WeightedFock
open FreeFock Amplification GaussianRecognition

theorem scalar_hasCornerScaling_weighted (u v : ℝ) (hv : 0<v) (hvu : v<u)
    (hunit : u^2+v^2=1) :
    HasCornerScaling scalarTrace (scalarSystem.generatedTopology scalarFlip) (u^2) := by
  sorry

end FreeGroupFactorMain.WeightedFock
end
end OAI
