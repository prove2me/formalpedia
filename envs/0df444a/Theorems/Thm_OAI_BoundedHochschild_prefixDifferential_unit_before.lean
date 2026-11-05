-- Prove2me | Theorems.Thm_OAI_BoundedHochschild_prefixDifferential_unit_before
-- name    : OAI.BoundedHochschild.prefixDifferential_unit_before
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T14:41:08.988236+00:00
-- url     : https://prove2.me/theorems/09e585a1-ab0f-42c9-aeab-7719dd741fa7
-- title:
--   The prefix differential vanishes on a unit inserted before the cut
-- statement:
--   Let $M$ be a unital C*-algebra, $h$ a cochain of degree $n+1$ and $r\in\mathbb N$. For a cochain $h$ of degree $n+1$ and $r\in\mathbb N$, the prefix differential is $d_rh=h^{\mathrm{left}}+\sum_{j\le n,\ j<r}(-1)^{j+1}h^{\mathrm{mid}}_j$ (`prefixDifferential h r`), where $h^{\mathrm{left}}(v_0,\dots)=v_0h(v_1,\dots)$ and $h^{\mathrm{mid}}_j$ multiplies the inputs $v_j,v_{j+1}$. The cochain $h$ vanishes on units before $r$ (`UnitZeroBefore h r`) when $h(\dots,1,\dots)=0$ whenever the $1$ is inserted at a position $i<r$. If $h$ vanishes on units before $r$ and $i<r$, then inserting $1$ at position $i$ of $n+2$ gives $d_rh(\dots,1,\dots)=0$.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with the listed `Definitions` imported in place of the upstream modules; the definitions are supporting code for this statement. Only the keyword `lemma`, where used upstream, becomes `theorem`, and a leading `include ... in` or `omit ... in` moves to the preamble. It is a step of the Lean proof of the vanishing of higher bounded Hochschild cohomology.
-- source:
--   OpenAI, Vanishing of higher bounded Hochschild cohomology, September 23, 2026, https://github.com/openai/math (paper: preprints/Vanishing-of-higher-bounded-Hochschild-cohomology-September-23-2026/paper.pdf; Apache License 2.0); Lean declaration `OAI.BoundedHochschild.prefixDifferential_unit_before`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/TracialCohomology/SlotHomotopy.lean#L602

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

theorem prefixDifferential_unit_before {n : ℕ} (h : Cochain M (n+1)) (r : ℕ)
    (hU : UnitZeroBefore h r) (i : Fin (n+1)) (hi : i.val<r) (v : Fin (n+1) → M) :
    prefixDifferential h r (i.castSucc.insertNth 1 v)=0 := by
  sorry

end BoundedHochschild
end
end OAI
