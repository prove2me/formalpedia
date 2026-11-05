-- Prove2me | Theorems.Thm_OAI_BoundedHochschild_KadisonRingrose_finite_homogeneous_typeI_primitive_of_abelian_diagonal
-- name    : OAI.BoundedHochschild.KadisonRingrose.finite_homogeneous_typeI_primitive_of_abelian_diagonal
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T14:41:01.451467+00:00
-- url     : https://prove2.me/theorems/024b76bc-c095-4dbe-9f95-be09ac72da16
-- title:
--   Homogeneous type I algebras with an abelian diagonal unit have bounded primitives
-- statement:
--   Throughout, $M$ is a unital C*-algebra with a partial order making it star-ordered, $X$ is a complex Banach space, and $e:X^*\to M$ is an isometric conjugate-linear isomorphism, so $M$ is a von Neumann algebra with predual $X$ (the Lean hypothesis `e`). Let $E=(e_{ij})_{i,j<d}$ be a matrix system with $e_{ij}^*=e_{ji}$, $e_{ij}e_{kl}=\delta_{jk}e_{il}$ and $\sum_ie_{ii}=1$ (`MatrixSystem M d`), and suppose some diagonal unit $e_{ii}$ is an abelian projection (`FinitePathMain.AbelianProjection`). Then every bounded cocycle $f$ of degree $n+1$ on $M$ has a primitive $g$ of degree $n$ with $\|g\|\le\|f\|$ and $\partial g=f$. Here a cochain of degree $k$ is a bounded complex $k$-linear map $M^k\to M$, and $\partial$ (`differentialValue`) is the Hochschild differential $(\partial f)(v_0,\dots,v_k)=v_0f(v_1,\dots,v_k)+\sum_{j<k}(-1)^{j+1}f(\dots,v_jv_{j+1},\dots)+(-1)^{k+1}f(v_0,\dots,v_{k-1})v_k$.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with the listed `Definitions` imported in place of the upstream modules; the definitions are supporting code for this statement. Only the keyword `lemma`, where used upstream, becomes `theorem`, and a leading `include ... in` or `omit ... in` moves to the preamble. It is a step of the Lean proof of the vanishing of higher bounded Hochschild cohomology.
-- source:
--   OpenAI, Vanishing of higher bounded Hochschild cohomology, September 23, 2026, https://github.com/openai/math (paper: preprints/Vanishing-of-higher-bounded-Hochschild-cohomology-September-23-2026/paper.pdf; Apache License 2.0); Lean declaration `OAI.BoundedHochschild.KadisonRingrose.finite_homogeneous_typeI_primitive_of_abelian_diagonal`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/BoundedHochschild/HomogeneousTypeIPrimitives.lean#L89

import Mathlib
import Definitions.Def_KadisonRingroseSupport2

namespace OAI

noncomputable section

open Filter Topology
open scoped ComplexOrder BigOperators

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildMatrixSystems HochschildSakai

universe u

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

theorem finite_homogeneous_typeI_primitive_of_abelian_diagonal
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) {d : ℕ} (E : MatrixSystem M d) (i : Fin d)
    (hi : FinitePathMain.AbelianProjection (E.entry i i))
    {n : ℕ} (f : Cochain M (n + 1)) (hf : ∀ x, differentialValue f x = 0) :
    ∃ g : Cochain M n, ‖g‖ ≤ ‖f‖ ∧ ∀ x, differentialValue g x = f x := by
  sorry

end KadisonRingrose
end BoundedHochschild
end
end OAI
