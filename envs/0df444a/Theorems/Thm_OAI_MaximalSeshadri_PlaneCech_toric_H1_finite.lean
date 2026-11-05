-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_PlaneCech_toric_H1_finite
-- name    : OAI.MaximalSeshadri.PlaneCech.toric_H1_finite
-- status  : Open
-- author  : @wurtle
-- created : 2026-11-04T15:10:42.954076+00:00
-- url     : https://prove2.me/theorems/e50910c4-11ce-42bf-a65b-15dc0e62e290
-- title:
--   Finiteness of toric H^1 in a Laurent module
-- statement:
--   With $V_i$ and clearing as above, let $A,B,C$ be $K$-submodules of $M$ stable under `coneA`, `coneB` and `coneC 0`, containing $V_0,V_0,V_1$ respectively and generated over those cones by $g_0,g_0,g_1$. Then the quotient of `cycles A B C` (triples in $A\times B\times C$ summing to zero) by `vertexBoundaries A B C V` is finite over $K$.
--
--   **Notation.** `cycles A B C` is the submodule of $A\times B\times C$ of triples with zero sum.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with `Definitions` files of this development imported in place of the upstream modules; these are supporting code for the statement.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0); Lean declaration `OAI.MaximalSeshadri.PlaneCech.toric_H1_finite`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Cohomology/ToricH1.lean#L82

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

namespace OAI

section

namespace MaximalSeshadri.PlaneCech
noncomputable section
open LaurentPlane
variable {K M : Type*} [Field K] [AddCommGroup M]
  [Module K M]

variable [Module (LaurentPlane.Ring K) M] [IsScalarTower K (LaurentPlane.Ring K) M]

theorem toric_H1_finite (V : Fin 3 → Submodule K M)
    (stable : ∀ i z, z ∈ vertexCone i → ∀ x ∈ V i, T (K := K) z • x ∈ V i)
    {ι : Fin 3 → Type*} [∀ i, Fintype (ι i)] (g : ∀ i, ι i → M)
    (hg : ∀ i a, g i a ∈ V i)
    (clear : ∀ i j (x : M), x ∈ V j →
      ∃ d : ℕ, T (K := K) (d • (weight j-weight i)) • x ∈ V i)
    (A B C : Submodule K M)
    (hA : ∀ z ∈ coneA, ∀ x ∈ A, T (K := K) z • x ∈ A)
    (hB : ∀ z ∈ coneB, ∀ x ∈ B, T (K := K) z • x ∈ B)
    (hC : ∀ z ∈ coneC 0, ∀ x ∈ C, T (K := K) z • x ∈ C)
    (incA : V 0 ≤ A) (incB : V 0 ≤ B) (incC : V 1 ≤ C)
    (genA : A = monomialSpan (K := K) coneA (g 0)) (genB : B = monomialSpan (K := K) coneB (g 0))
    (genC : C = monomialSpan (K := K) (coneC 0) (g 1)) :
    Module.Finite K ((cycles A B C) ⧸ vertexBoundaries A B C V) := by
  sorry

end
end MaximalSeshadri.PlaneCech
end
end OAI
