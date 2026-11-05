-- Prove2me | Theorems.Thm_OAI_BoundedHochschild_prefixDifferential_unit_at
-- name    : OAI.BoundedHochschild.prefixDifferential_unit_at
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T14:41:24.408237+00:00
-- url     : https://prove2.me/theorems/05f7ab35-d5e4-4593-9b69-fe82f1bbf999
-- title:
--   The prefix differential at the first unit position
-- statement:
--   Let $M$ be a unital C*-algebra and $h$ a cochain of degree $n+1$, with $r<n+1$. For a cochain $h$ of degree $n+1$ and $r\in\mathbb N$, the prefix differential is $d_rh=h^{\mathrm{left}}+\sum_{j\le n,\ j<r}(-1)^{j+1}h^{\mathrm{mid}}_j$ (`prefixDifferential h r`), where $h^{\mathrm{left}}(v_0,\dots)=v_0h(v_1,\dots)$ and $h^{\mathrm{mid}}_j$ multiplies the inputs $v_j,v_{j+1}$. The cochain $h$ vanishes on units before $r$ (`UnitZeroBefore h r`) when $h(\dots,1,\dots)=0$ whenever the $1$ is inserted at a position $i<r$. If $h$ vanishes on units before $r$, then inserting $1$ at position $r$ gives
--
--   $$d_rh(\dots,1,\dots)=(-1)^r\,h(v).$$
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with the listed `Definitions` imported in place of the upstream modules; the definitions are supporting code for this statement. Only the keyword `lemma`, where used upstream, becomes `theorem`, and a leading `include ... in` or `omit ... in` moves to the preamble. It is a step of the Lean proof of the vanishing of higher bounded Hochschild cohomology.
-- source:
--   OpenAI, Vanishing of higher bounded Hochschild cohomology, September 23, 2026, https://github.com/openai/math (paper: preprints/Vanishing-of-higher-bounded-Hochschild-cohomology-September-23-2026/paper.pdf; Apache License 2.0); Lean declaration `OAI.BoundedHochschild.prefixDifferential_unit_at`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/TracialCohomology/SlotHomotopy.lean#L607

import Mathlib
import Definitions.Def_KadisonRingroseSupport2

namespace OAI

noncomputable section
open Filter Topology MeasureTheory
open scoped BigOperators ComplexOrder InnerProductSpace ComplexStarModule CStarAlgebra

namespace BoundedHochschild
open HochschildNormalPart
universe u
variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

end BoundedHochschild

namespace BoundedHochschild
open HochschildNormalPart
universe u v
variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

theorem prefixDifferential_unit_at {n : ℕ} (h : Cochain M (n+1)) (r : Fin (n+1))
    (hU : UnitZeroBefore h r.val) (v : Fin (n+1) → M) :
    prefixDifferential h r.val (r.castSucc.insertNth 1 v)=((-1:ℂ)^r.val) • h v := by
  sorry

end BoundedHochschild
end
end OAI
