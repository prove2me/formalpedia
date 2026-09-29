-- Prove2me | Theorems.Thm_NumberField_localChar_ne_one_of_range_norm_ne_top_of_isIdeleClassChar_of_finrank_eq_two
-- name    : NumberField.localChar_ne_one_of_range_norm_ne_top_of_isIdeleClassChar_of_finrank_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/71f96b63-17c3-58a3-9552-ef7c12948b0c
-- title:
--   Local components of an idele class character at non-norm places
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra of degree $\operatorname{finrank}_K L = 2$, and let $\eta \colon (\mathbf{A}_K)^\times \to \mathbf{C}^\times$ be a continuous group homomorphism on the units of the adele ring of $K$ which satisfies `IsIdeleClassChar`, i.e. $\eta$ kills the image of $K^\times$ under the diagonal embedding, and which is not the trivial homomorphism. Assume two local-norm conditions: for every nonzero prime $v$ of $\mathcal{O}_K$ and every $x \in (K_v)^\times$ lying in the image, on units, of the algebra norm $L \otimes_K K_v \to K_v$, one has $\operatorname{localChar} \eta\, v\, (x) = 1$, where $\operatorname{localChar} \eta\, v$ is $\eta$ evaluated at the idele whose $v$-component is $x$ and all of whose other components (finite and infinite) are $1$; and likewise, for every infinite place $w$ of $K$ and every unit $x$ of the completion $K_w$ that is a norm from $L \otimes_K K_w$, one has $\operatorname{archLocalChar} \eta\, w\, (x) = 1$, the idele now being concentrated at $w$. The conclusion is the conjunction of two assertions: for every prime $v$ for which the image of the unit norm map from $L \otimes_K K_v$ is not all of $(K_v)^\times$, the homomorphism $\operatorname{localChar} \eta\, v$ is nontrivial; and for every infinite place $w$ for which the image of the unit norm map from $L \otimes_K K_w$ is not all of $(K_w)^\times$, the homomorphism $\operatorname{archLocalChar} \eta\, w$ is nontrivial.
--
--   This is the local–global compatibility of the quadratic character attached to a degree-two extension $L/K$: a nontrivial character of the idele class group killing all local norms must have nontrivial local component at each place that is not locally a norm place. It is used in the proof that the set of places of $K$ at which not every local unit is a norm from $L$ is finite of even cardinality.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_localChar_ne_one_of_range_norm_ne_top_of_isIdeleClassChar_of_finrank_eq_two.lean

import Mathlib
import Definitions.Def_Mathlib_RightActionInstances
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.TateGlobal AutomorphicForm IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

theorem NumberField.localChar_ne_one_of_range_norm_ne_top_of_isIdeleClassChar_of_finrank_eq_two
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2)
    (η : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hη : IsIdeleClassChar (𝓞 K) K η) (hcont : Continuous η)
    (hne : η ≠ 1)
    (hfin : ∀ (v : HeightOneSpectrum (𝓞 K)) (x : (v.adicCompletion K)ˣ),
      x ∈ (Units.map (Algebra.norm (v.adicCompletion K) :
          L ⊗[K] v.adicCompletion K →* v.adicCompletion K)).range →
        localChar η v x = 1)
    (hinf : ∀ (w : InfinitePlace K) (x : (w.Completion)ˣ),
      x ∈ (Units.map (Algebra.norm w.Completion : L ⊗[K] w.Completion →* w.Completion)).range →
        archLocalChar η w x = 1) :
    (∀ v : HeightOneSpectrum (𝓞 K),
      (Units.map (Algebra.norm (v.adicCompletion K) :
          L ⊗[K] v.adicCompletion K →* v.adicCompletion K)).range ≠ ⊤ →
        localChar η v ≠ 1) ∧
    (∀ w : InfinitePlace K,
      (Units.map (Algebra.norm w.Completion : L ⊗[K] w.Completion →* w.Completion)).range ≠ ⊤ →
        archLocalChar η w ≠ 1) := by sorry
