-- Prove2me | Theorems.Thm_OAI_Cotype_projectionSubset_union
-- name    : OAI.Cotype.projectionSubset_union
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T19:53:57.361305+00:00
-- url     : https://prove2.me/theorems/6851017c-878d-4b4e-bdbe-a48a86b2a2b2
-- title:
--   Products of commuting projections over a union
-- statement:
--   These notions belong to a proof that a real Banach space $X$ with the approximation property is K-convex (the Rademacher projection is bounded on $L_2(\{\pm1\}^n;X)$ uniformly in $n$) if and only if $X$ and its dual $X^*$ both have finite cotype. The converse direction shows that such $X$ has nontrivial type, i.e. does not contain $\ell_1^n$ uniformly, and then derives K-convexity from a power-gap estimate for commuting coordinate projections. For commuting bounded projections $P_1,\dots,P_m$ on $X$, products are taken in a fixed order, $P_S=\prod_{i\in S}P_i$, and the coordinate semigroup is $T(r)=\prod_i\bigl(P_i+r(1-P_i)\bigr)$. Let $P_1,\dots,P_n$ be commuting idempotent operators on a real normed space. For $S,R\subseteq\{1,\dots,n\}$,
--   $$
--   P_S\,P_R=P_{S\cup R}.
--   $$
--
--   Repeated factors collapse because each $P_i$ is idempotent.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Cotype/ProjectionProducts.lean#L50-L72

import Mathlib
import Definitions.Def_Cotype
import Definitions.Def_OAI_Analysis_Cotype_ComplexDualLift
import Definitions.Def_OAI_Analysis_Cotype_Cube
import Definitions.Def_OAI_Analysis_Cotype_Target
import Definitions.Def_OAI_Analysis_Cotype_Moments
import Definitions.Def_OAI_Analysis_Cotype_Fourier
import Definitions.Def_OAI_Analysis_Cotype_ScalarWalsh
import Definitions.Def_OAI_Analysis_Cotype_VectorWalsh
import Definitions.Def_OAI_Analysis_Cotype_WalshNorm
import Definitions.Def_OAI_Analysis_Cotype_WalshCoordinates
import Definitions.Def_OAI_Analysis_Cotype_WalshDuality
import Definitions.Def_OAI_Analysis_Cotype_CubeNoise
import Definitions.Def_OAI_Analysis_Cotype_ProjectionProducts

open OAI OAI.Cotype
open scoped BigOperators
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem OAI.Cotype.projectionSubset_union {n : ℕ} (P : Fin n → X →L[ℝ] X)
    (hp : ∀ i, P i * P i = P i) (hc : ∀ i j, Commute (P i) (P j))
    (ε η : Cube n) :
    projectionSubset P ε * projectionSubset P η =
      projectionSubset P (fun i => ε i || η i) := by sorry
