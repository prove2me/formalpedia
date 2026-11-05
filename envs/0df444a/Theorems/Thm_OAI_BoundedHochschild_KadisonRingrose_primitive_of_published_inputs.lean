-- Prove2me | Theorems.Thm_OAI_BoundedHochschild_KadisonRingrose_primitive_of_published_inputs
-- name    : OAI.BoundedHochschild.KadisonRingrose.primitive_of_published_inputs
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T14:42:15.786177+00:00
-- url     : https://prove2.me/theorems/bc70a102-461c-4b8b-9273-f3e618c2f7be
-- title:
--   Assembling a primitive from a central decomposition and classical vanishing
-- statement:
--   Throughout, $M$ is a unital C*-algebra with a partial order making it star-ordered, $X$ is a complex Banach space, and $e:X^*\to M$ is an isometric conjugate-linear isomorphism, so $M$ is a von Neumann algebra with predual $X$ (the Lean hypothesis `e`). A family $(a_i)$ converges in the predual sense to $b$ (`PredualTendsto`) when $e^{-1}(a_i)(z)\to e^{-1}(b)(z)$ for every $z\in X$. A cochain of degree $k$ is a bounded complex $k$-linear map $M^k\to M$, and $\partial$ (`differentialValue`) is the Hochschild differential $(\partial f)(v_0,\dots,v_k)=v_0f(v_1,\dots,v_k)+\sum_{j<k}(-1)^{j+1}f(\dots,v_jv_{j+1},\dots)+(-1)^{k+1}f(v_0,\dots,v_{k-1})v_k$. Assume a central decomposition of $M$ (`CentralDecompositionInput M`): orthogonal central projections indexed by `Option Index` that separate points, where the corner at `none` has no type II$_1$ central summand and each other corner is tracial of type II$_1$ (`TracialTypeII`). Assume also classical vanishing (`ClassicalVanishingInput`: every W*-algebra with no type II$_1$ summand has primitives for all bounded cocycles of degree $\ge2$). Then every bounded cocycle $f$ of degree $n+2$ on $M$ has a bounded primitive.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with the listed `Definitions` imported in place of the upstream modules; the definitions are supporting code for this statement. Only the keyword `lemma`, where used upstream, becomes `theorem`, and a leading `include ... in` or `omit ... in` moves to the preamble. It is a step of the Lean proof of the vanishing of higher bounded Hochschild cohomology.
-- source:
--   OpenAI, Vanishing of higher bounded Hochschild cohomology, September 23, 2026, https://github.com/openai/math (paper: preprints/Vanishing-of-higher-bounded-Hochschild-cohomology-September-23-2026/paper.pdf; Apache License 2.0); Lean declaration `OAI.BoundedHochschild.KadisonRingrose.primitive_of_published_inputs`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/BoundedHochschild/Conditional.lean#L75

import Mathlib
import Definitions.Def_KadisonRingroseSupport2

namespace OAI

noncomputable section

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildCorners
open scoped ComplexOrder

universe u

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

theorem primitive_of_published_inputs (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (hdecomp : CentralDecompositionInput M) (hclassical : ClassicalVanishingInput.{u})
    {n : ℕ} (f : Cochain M (n + 2)) (hf : ∀ x, differentialValue f x = 0) :
    ∃ g : Cochain M (n + 1), ∀ x, differentialValue g x = f x := by
  sorry

end KadisonRingrose
end BoundedHochschild
end
end OAI
