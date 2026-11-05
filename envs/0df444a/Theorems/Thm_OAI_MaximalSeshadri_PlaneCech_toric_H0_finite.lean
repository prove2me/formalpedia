-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_PlaneCech_toric_H0_finite
-- name    : OAI.MaximalSeshadri.PlaneCech.toric_H0_finite
-- status  : Open
-- author  : @wurtle
-- created : 2026-11-04T15:17:46.771199+00:00
-- url     : https://prove2.me/theorems/d8dcf01d-51ef-4e04-88a6-4f6e62b3f177
-- title:
--   Finiteness of the triple intersection in a Laurent module
-- statement:
--   Let $K$ be a field and $M$ a module over the Laurent ring $K[\mathbb Z^2]$. Let $V_0,V_1,V_2$ be $K$-submodules, stable under the monomials of the vertex cones, each the monomial span of a finite family $g_i\subset V_i$ over its cone, and such that for all $i,j$ and $x\in V_j$ some $T^{d(w_j-w_i)}x$ lies in $V_i$. Then $V_0\cap V_1\cap V_2$ is finite over $K$.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with `Definitions` files of this development imported in place of the upstream modules; these are supporting code for the statement.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0); Lean declaration `OAI.MaximalSeshadri.PlaneCech.toric_H0_finite`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Cohomology/ToricH0.lean#L20

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

namespace OAI

section

namespace MaximalSeshadri.PlaneCech
noncomputable section
open LaurentPlane
variable {K M : Type*} [Field K] [AddCommGroup M]
  [Module K M] [Module (LaurentPlane.Ring K) M] [IsScalarTower K (LaurentPlane.Ring K) M]

theorem toric_H0_finite (V : Fin 3 → Submodule K M)
    (stable : ∀ i z, z ∈ vertexCone i → ∀ x ∈ V i, T (K := K) z • x ∈ V i)
    {ι : Fin 3 → Type*} [∀ i, Fintype (ι i)] (g : ∀ i, ι i → M)
    (hg : ∀ i a, g i a ∈ V i)
    (hgen : ∀ i, V i = monomialSpan (K := K) (vertexCone i) (g i))
    (clear : ∀ i j (x : M), x ∈ V j →
      ∃ d : ℕ, T (K := K) (d • (weight j-weight i)) • x ∈ V i) :
    Module.Finite K ↥((V 0 ⊓ V 1) ⊓ V 2) := by
  sorry

end
end MaximalSeshadri.PlaneCech
end
end OAI
