-- Prove2me | Theorems.Thm_OAI_BoundedHochschild_prefixDifferential_before_normal
-- name    : OAI.BoundedHochschild.prefixDifferential_before_normal
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T14:41:22.074539+00:00
-- url     : https://prove2.me/theorems/3c01eeae-2d61-4d16-87ca-52a162aeee64
-- title:
--   The prefix differential preserves normality below its cut
-- statement:
--   Throughout, $M$ is a unital C*-algebra (no order is assumed), $X$ is a complex Banach space, and $e:X^*\to M$ is an isometric conjugate-linear isomorphism, so $M$ is a von Neumann algebra with predual $X$ (the Lean hypothesis `e`). A family $(a_i)$ converges in the predual sense to $b$ (`PredualTendsto`) when $e^{-1}(a_i)(z)\to e^{-1}(b)(z)$ for every $z\in X$. For a cochain $f$ of degree $n+1$, a position $i$ and values $v$ for the other slots, the slice `sliceAt f i v` is the bounded linear map obtained by letting only slot $i$ vary. A bounded operator $L$ on $M$ has a preadjoint (`HasPreadjoint e L`) when for each $z\in X$ there is $z'\in X$ with $e^{-1}(L(a))(z)=e^{-1}(a)(z')$ for all $a$, i.e. when it is ultraweakly continuous. For a cochain $h$ of degree $n+1$ and $r\in\mathbb N$, the prefix differential is $d_rh=h^{\mathrm{left}}+\sum_{j\le n,\ j<r}(-1)^{j+1}h^{\mathrm{mid}}_j$ (`prefixDifferential h r`), where $h^{\mathrm{left}}(v_0,\dots)=v_0h(v_1,\dots)$ and $h^{\mathrm{mid}}_j$ multiplies the inputs $v_j,v_{j+1}$. If every slice of $h$ in a position below $r$ is normal (`NormalBefore e h r`), then for every position $i\le n$ with $i\le r$, every slice of $d_rh$ (a cochain with $n+2$ slots) at position $i$ has a preadjoint.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with the listed `Definitions` imported in place of the upstream modules; the definitions are supporting code for this statement. Only the keyword `lemma`, where used upstream, becomes `theorem`, and a leading `include ... in` or `omit ... in` moves to the preamble. It is a step of the Lean proof of the vanishing of higher bounded Hochschild cohomology.
-- source:
--   OpenAI, Vanishing of higher bounded Hochschild cohomology, September 23, 2026, https://github.com/openai/math (paper: preprints/Vanishing-of-higher-bounded-Hochschild-cohomology-September-23-2026/paper.pdf; Apache License 2.0); Lean declaration `OAI.BoundedHochschild.prefixDifferential_before_normal`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/TracialCohomology/SlotHomotopy.lean#L533

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

theorem prefixDifferential_before_normal {n : ℕ} (h : Cochain M (n+1)) (r : ℕ)
    (hN : NormalBefore e h r) (i : Fin (n+1)) (hi : i.val≤r) (v : Fin (n+1) → M) :
    HasPreadjoint e (sliceAt (prefixDifferential h r) i.castSucc v) := by
  sorry

end BoundedHochschild
end
end OAI
