-- Prove2me | Theorems.Thm_OAI_FreeGroupFactorMain_WeightedFock_weightedFull_right
-- name    : OAI.FreeGroupFactorMain.WeightedFock.weightedFull_right
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T02:56:09.630087+00:00
-- url     : https://prove2.me/theorems/59a695fc-c0ac-4aa6-9989-f2d405f15849
-- title:
--   The right-edge operator vanishes on the normal hull
-- statement:
--   Fix real numbers $0<v<u$. Consider the full two-vertex path Fock space with edge labels in $\mathbb N$, the operators $S_i=uc_{i,\mathrm{true}}+vc_{i,\mathrm{false}}+\text{h.c.}$ built from creation operators, the coordinate projection $P$ onto paths starting at the vertex $\mathrm{true}$, and the ambient von Neumann algebra $\{P,S_i\}''$. Let $\mathrm{PRange}$ be the range of $P$, and let $\mathrm{representedAmbient}(u,v)$ be the corner of the ambient algebra by $P$, represented on $\mathrm{PRange}$. Let $\mathcal X$ be the weighted Gaussian system on $\mathrm{PRange}$ with the restricted vacuum as root, and let $\sigma$ be the scalar flip of its index set. Let $R$ be the operator on $\mathrm{PRange}$ obtained by compressing the right-edge operator, the commutant counterpart of the polar part of an edge operator. Let $Q$ be the orthogonal projection onto the normal hull of $\mathcal X$, the closed linear span of the family of vectors attached to the system. Then
--
--   $$R(1-Q)=R.$$
--
--   Equivalently $RQ=0$. This is the second relation showing that the weighted system meets the fullness hypothesis of the reduction argument.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with the listed `Definitions` imported in place of the upstream modules; the definitions are supporting code for this statement.
-- source:
--   OpenAI, An isomorphism of the free group factors, September 23, 2026, https://github.com/openai/math (paper: preprints/An-isomorphism-of-the-free-group-factors-September-23-2026/An-isomorphism-of-the-free-group-factors-September-23-2026.pdf; Lean: lean/OAI/Analysis/FreeGroupFactor and lean/OAI/Analysis/InterpolatedFactors, Apache License 2.0); Lean declaration `OAI.FreeGroupFactorMain.WeightedFock.weightedFull_right`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/InterpolatedFactors/Restriction.lean#L157

import Mathlib
import Definitions.Def_FreeGroupFactorProof18

namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7

section
namespace FreeGroupFactorMain.FullReducingCorner
open Amplification GaussianRecognition
variable {A : Type u_1} {B : Type u_2} [CStarAlgebra A] [CStarAlgebra B]

variable {E : Type u_3} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (K : Submodule ℂ E) [CompleteSpace K]

variable (s : Set (E →L[ℂ] E))
variable (hps : K.starProjection∈StarSubalgebra.centralizer ℂ s)
variable (v : E →L[ℂ] E) (hvs : v∈StarSubalgebra.centralizer ℂ s)
variable (hpv : K.starProjection*v=v) (hvr : v*(1-K.starProjection)=v) (hvi : star v*v=1-K.starProjection)

end FreeGroupFactorMain.FullReducingCorner

namespace FreeGroupFactorMain.GaussianRecognition.System
open  FullReducingCorner
variable {A : Type u_5} {E : Type u_6} {I : Type u_7} [Ring A] [StarRing A] [Algebra ℂ A]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {covariance : I → I → A → A} (X : System A E I covariance)

variable (σ : I → I) (v : E →L[ℂ] E) (hvs : v∈StarSubalgebra.centralizer ℂ (X.generators σ))
variable (hpv : X.normalHull.starProjection*v=v) (hvr : v*(1-X.normalHull.starProjection)=v)
variable (hvi : star v*v=1-X.normalHull.starProjection)

end FreeGroupFactorMain.GaussianRecognition.System

end

namespace FreeGroupFactorMain.WeightedFock
open FreeFock Amplification GaussianRecognition
variable (u v : ℝ) (hv : 0<v) (hvu : v<u)

theorem weightedFull_right :
    pRightEdge u v*(1-(weightedSystem u v hv hvu).normalHull.starProjection)=pRightEdge u v := by
  sorry

end FreeGroupFactorMain.WeightedFock
end
end OAI
