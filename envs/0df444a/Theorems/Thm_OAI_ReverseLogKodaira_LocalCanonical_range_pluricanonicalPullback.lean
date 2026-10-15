-- Prove2me | Theorems.Thm_OAI_ReverseLogKodaira_LocalCanonical_range_pluricanonicalPullback
-- name    : OAI.ReverseLogKodaira.LocalCanonical.range_pluricanonicalPullback
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:58:54.438123+00:00
-- url     : https://prove2.me/theorems/cef28df0-0364-45a3-b54b-332fc647d8c3
-- title:
--   The image of regular pluricanonical forms in rational ones is spanned by tensors of wedges of exact differentials
-- statement:
--   Let $R$ be a commutative ring, $A$ a commutative $R$-algebra and $K$ a field that is an $A$-algebra, such that $R\to A\to K$ is the given $R$-algebra structure of $K$. For $a\in A$ write $\bar a$ for its image in $K$. For $n,m\in\mathbb{N}$ let
--   $$\pi\colon\big(\textstyle\bigwedge^n_A\Omega_{A/R}\big)^{\otimes_A m}\longrightarrow\big(\textstyle\bigwedge^n_K\Omega_{K/R}\big)^{\otimes_K m}$$
--   be the $A$-linear map induced, on every exterior and tensor factor, by the map of Kähler differentials $\Omega_{A/R}\to\Omega_{K/R}$, $da\mapsto d\bar a$. Then the image of $\pi$ is the $A$-submodule
--
--   $$
--   \operatorname{im}\pi=\operatorname{span}_A\Big\{\textstyle\bigotimes_{j=1}^{m}\big(d\bar a_{j,1}\wedge\cdots\wedge d\bar a_{j,n}\big)\;:\;a_{j,i}\in A\ \text{for }1\le j\le m,\ 1\le i\le n\Big\}.
--   $$
--
--   When $A=\mathcal{O}_X(W)$ is the coordinate ring of a nonempty affine open $W$ of a smooth variety $X$ over $R=\mathbb{C}$, $K=K(X)$ and $n=\dim X$, the right-hand side is the lattice of $m$-pluricanonical forms that are regular on $W$. The theorem identifies this lattice with the image of the module of algebraic pluricanonical forms on $W$, so every regular form can be represented by an element of $\big(\bigwedge^n_A\Omega_{A/R}\big)^{\otimes_A m}$. This is how numerators of logarithmic forms are produced and how regularity of specialized forms on fibres is verified.
--
--   **Formalization Note** The map $\pi$ is `pluricanonicalPullback R A K n m`, and the span is taken inside the $K$-module $\big(\bigwedge^n_K\Omega_{K/R}\big)^{\otimes_K m}$ regarded as an $A$-module. For $m=0$ both tensor powers are the base rings and both sides are the image of $A$ in $K$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/AlgebraicGeometry/LogKodaira/LocalCanonical.lean#L64-L85

import Mathlib
import Definitions.Def_LogKodairaFiberNegative
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_Basic
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_Adjunction
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_BaseChange
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_RelativeCanonical
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_Specialization
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_LocalCanonical

open OAI OAI.ReverseLogKodaira OAI.ReverseLogKodaira.LocalCanonical
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
open scoped TensorProduct
variable (R A K : Type*) [CommRing R] [CommRing A] [Field K]
  [Algebra R A] [Algebra A K] [Algebra R K] [IsScalarTower R A K]

theorem OAI.ReverseLogKodaira.LocalCanonical.range_pluricanonicalPullback (n m : ℕ) :
    LinearMap.range (pluricanonicalPullback R A K n m) =
      Submodule.span A (Set.range fun a : Fin m → Fin n → A =>
        PiTensorProduct.tprod K fun j => exteriorPower.ιMulti K n fun i =>
          KaehlerDifferential.D R K (algebraMap A K (a j i))) := by sorry
