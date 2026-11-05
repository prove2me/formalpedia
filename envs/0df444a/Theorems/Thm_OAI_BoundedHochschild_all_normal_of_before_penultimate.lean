-- Prove2me | Theorems.Thm_OAI_BoundedHochschild_all_normal_of_before_penultimate
-- name    : OAI.BoundedHochschild.all_normal_of_before_penultimate
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T14:40:27.598754+00:00
-- url     : https://prove2.me/theorems/1627248c-b45a-45fc-aa27-3721f7625e75
-- title:
--   From normality before the penultimate slot to normality in every slot
-- statement:
--   Throughout, $M$ is a unital C*-algebra (no order is assumed), $X$ is a complex Banach space, and $e:X^*\to M$ is an isometric conjugate-linear isomorphism, so $M$ is a von Neumann algebra with predual $X$ (the Lean hypothesis `e`). A family $(a_i)$ converges in the predual sense to $b$ (`PredualTendsto`) when $e^{-1}(a_i)(z)\to e^{-1}(b)(z)$ for every $z\in X$. For a cochain $f$ of degree $n+1$, a position $i$ and values $v$ for the other slots, the slice `sliceAt f i v` is the bounded linear map obtained by letting only slot $i$ vary. A bounded operator $L$ on $M$ has a preadjoint (`HasPreadjoint e L`) when for each $z\in X$ there is $z'\in X$ with $e^{-1}(L(a))(z)=e^{-1}(a)(z')$ for all $a$, i.e. when it is ultraweakly continuous. Let $f$ be a bounded cocycle of degree $n+2$ with every slice in a position below $n+1$ normal (`NormalBefore e f (n+1)`). Then every slice of $f$, in every position, has a preadjoint.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with the listed `Definitions` imported in place of the upstream modules; the definitions are supporting code for this statement. Only the keyword `lemma`, where used upstream, becomes `theorem`, and a leading `include ... in` or `omit ... in` moves to the preamble. It is a step of the Lean proof of the vanishing of higher bounded Hochschild cohomology.
-- source:
--   OpenAI, Vanishing of higher bounded Hochschild cohomology, September 23, 2026, https://github.com/openai/math (paper: preprints/Vanishing-of-higher-bounded-Hochschild-cohomology-September-23-2026/paper.pdf; Apache License 2.0); Lean declaration `OAI.BoundedHochschild.all_normal_of_before_penultimate`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/TracialCohomology/HilbertFactorization.lean#L125

import Mathlib
import Definitions.Def_KadisonRingroseSupport2

namespace OAI

noncomputable section
open Filter Topology MeasureTheory
open scoped BigOperators ComplexOrder InnerProductSpace ComplexStarModule CStarAlgebra

namespace HochschildNormalPart
universe u
variable (M : Type u) [CStarAlgebra M]

attribute [instance] SharedHilbertFactor.group SharedHilbertFactor.inner SharedHilbertFactor.complete

end HochschildNormalPart

namespace BoundedHochschild
open HochschildNormalPart
universe u
variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

theorem all_normal_of_before_penultimate {n : ℕ} (f : Cochain M (n+2))
    (hf : ∀ v,differentialValue f v=0) (hN : NormalBefore e f (n+1)) :
    ∀ (i : Fin (n+2)) v,HasPreadjoint e (sliceAt f i v) := by
  sorry

end BoundedHochschild
end
end OAI
