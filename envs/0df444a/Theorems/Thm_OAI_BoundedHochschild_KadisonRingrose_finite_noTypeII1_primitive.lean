-- Prove2me | Theorems.Thm_OAI_BoundedHochschild_KadisonRingrose_finite_noTypeII1_primitive
-- name    : OAI.BoundedHochschild.KadisonRingrose.finite_noTypeII1_primitive
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T14:42:20.643827+00:00
-- url     : https://prove2.me/theorems/88bd7d94-ebd0-475b-9fbf-abe38bf9919f
-- title:
--   Finite algebras with no type II$_1$ summand have bounded primitives
-- statement:
--   Throughout, $M$ is a unital C*-algebra with a partial order making it star-ordered, $X$ is a complex Banach space, and $e:X^*\to M$ is an isometric conjugate-linear isomorphism, so $M$ is a von Neumann algebra with predual $X$ (the Lean hypothesis `e`). Suppose $M$ is finite (every isometry is unitary, `FiniteAlgebra M`) and has no type II$_1$ central summand (`NoTypeII1Summand M`: a central projection $z$ whose corner is finite and has no type I central part must vanish). Then every bounded cocycle $f$ of degree $n+2$ has a primitive $g$ of degree $n+1$ with
--
--   $$\|g\|\le\|f\|+(n+1)\|f\|,\qquad\partial g=f.$$
--
--   Here a cochain of degree $k$ is a bounded complex $k$-linear map $M^k\to M$, and $\partial$ (`differentialValue`) is the Hochschild differential $(\partial f)(v_0,\dots,v_k)=v_0f(v_1,\dots,v_k)+\sum_{j<k}(-1)^{j+1}f(\dots,v_jv_{j+1},\dots)+(-1)^{k+1}f(v_0,\dots,v_{k-1})v_k$.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with the listed `Definitions` imported in place of the upstream modules; the definitions are supporting code for this statement. Only the keyword `lemma`, where used upstream, becomes `theorem`, and a leading `include ... in` or `omit ... in` moves to the preamble. It is a step of the Lean proof of the vanishing of higher bounded Hochschild cohomology.
-- source:
--   OpenAI, Vanishing of higher bounded Hochschild cohomology, September 23, 2026, https://github.com/openai/math (paper: preprints/Vanishing-of-higher-bounded-Hochschild-cohomology-September-23-2026/paper.pdf; Apache License 2.0); Lean declaration `OAI.BoundedHochschild.KadisonRingrose.finite_noTypeII1_primitive`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/BoundedHochschild/FiniteTypeIVanishing.lean#L72

import Mathlib
import Definitions.Def_KadisonRingroseSupport2

namespace OAI

noncomputable section

open scoped ComplexOrder

namespace BoundedHochschild.KadisonRingrose

open FinitePathMain HochschildCorners

universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

theorem finite_noTypeII1_primitive (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (hfinite : FiniteAlgebra M) (hno : NoTypeII1Summand M)
    {n : ℕ} (f : Cochain M (n + 2)) (hf : ∀ x, differentialValue f x = 0) :
    ∃ g : Cochain M (n + 1), ‖g‖ ≤ ‖f‖ + (n + 1) * ‖f‖ ∧
      ∀ x, differentialValue g x = f x := by
  sorry

end BoundedHochschild.KadisonRingrose
end
end OAI
