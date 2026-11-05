-- Prove2me | Theorems.Thm_OAI_BoundedHochschild_KadisonRingrose_normal_reduction_multimodular
-- name    : OAI.BoundedHochschild.KadisonRingrose.normal_reduction_multimodular
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T14:42:18.115972+00:00
-- url     : https://prove2.me/theorems/6f310064-cd7a-4ef5-b24f-7945e455775d
-- title:
--   Normal reduction of a multimodular cocycle
-- statement:
--   Let $M$ be a unital C*-algebra with predual $X$ through an isometric conjugate-linear isomorphism $e:X^*\to M$, and let $R\subseteq M$ be a *-subalgebra. Let $f$ be a bounded $(n+2)$-linear Hochschild cocycle on $M$ that is $R$-multimodular (`MultimodularOver R f`: it is $R$-linear on the left in the first slot and on the right in the last slot, and balanced across adjacent slots). Then there are a bounded $(n+2)$-cochain $F$ and a bounded $(n+1)$-cochain $b$ such that $F$ is separately normal (`SeparatelyNormal e F`: ultraweakly continuous in each slot), $F$ is $R$-multimodular, $\partial F=0$, and
--
--   $$f(x)=F(x)+(\partial b)(x)\quad\text{for all }x.$$
--
--   Here a cochain of degree $k$ is a bounded complex $k$-linear map $M^k\to M$, and $\partial$ (`differentialValue`) is the Hochschild differential $(\partial f)(v_0,\dots,v_k)=v_0f(v_1,\dots,v_k)+\sum_{j<k}(-1)^{j+1}f(\dots,v_jv_{j+1},\dots)+(-1)^{k+1}f(v_0,\dots,v_{k-1})v_k$.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with the listed `Definitions` imported in place of the upstream modules; the definitions are supporting code for this statement. Only the keyword `lemma`, where used upstream, becomes `theorem`, and a leading `include ... in` or `omit ... in` moves to the preamble. It is a step of the Lean proof of the vanishing of higher bounded Hochschild cohomology.
-- source:
--   OpenAI, Vanishing of higher bounded Hochschild cohomology, September 23, 2026, https://github.com/openai/math (paper: preprints/Vanishing-of-higher-bounded-Hochschild-cohomology-September-23-2026/paper.pdf; Apache License 2.0); Lean declaration `OAI.BoundedHochschild.KadisonRingrose.normal_reduction_multimodular`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/BoundedHochschild/MultimodularNormalReduction.lean#L112

import Mathlib
import Definitions.Def_KadisonRingroseSupport2

namespace OAI

noncomputable section

namespace BoundedHochschild.KadisonRingrose

universe u
variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

theorem normal_reduction_multimodular (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {n : ℕ} (R : StarSubalgebra ℂ M) (f : Cochain M (n + 2))
    (hf : ∀ x, differentialValue f x = 0) (hM : MultimodularOver R f) :
    ∃ (F : Cochain M (n + 2)) (b : Cochain M (n + 1)),
      SeparatelyNormal e F ∧ MultimodularOver R F ∧
      (∀ x, differentialValue F x = 0) ∧ (∀ x, f x = F x + differentialValue b x) := by
  sorry

end BoundedHochschild.KadisonRingrose
end
end OAI
