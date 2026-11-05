-- Prove2me | Theorems.Thm_OAI_BoundedHochschild_KadisonRingrose_exists_unital_completelyPositive_extension
-- name    : OAI.BoundedHochschild.KadisonRingrose.exists_unital_completelyPositive_extension
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T14:40:17.535081+00:00
-- url     : https://prove2.me/theorems/31b4c204-de99-43c8-8500-ffb38544d8ef
-- title:
--   Arveson-type extension of a unital completely positive map on an operator system
-- statement:
--   Let $A$ be a unital C*-algebra with star-ordered partial order and $H$ a nontrivial complex Hilbert space. Let $S\subseteq A$ be a linear subspace containing $1$ and closed under $*$, and $\varphi:S\to B(H)$ a linear map with $\varphi(1)=1$ such that every amplification sends positive matrices over $S$ to positive matrices: if $X\in M_n(S)$ and $X\ge0$ in $M_n(A)$, then $(\varphi(X_{ij}))\ge0$. Then there is a completely positive map $\Phi:A\to B(H)$ (`CompletelyPositiveMap`) with $\Phi(1)=1$, $\|\Phi(a)\|\le\|a\|$ and $\Phi|_S=\varphi$.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with the listed `Definitions` imported in place of the upstream modules; the definitions are supporting code for this statement. Only the keyword `lemma`, where used upstream, becomes `theorem`, and a leading `include ... in` or `omit ... in` moves to the preamble. It is a step of the Lean proof of the vanishing of higher bounded Hochschild cohomology.
-- source:
--   OpenAI, Vanishing of higher bounded Hochschild cohomology, September 23, 2026, https://github.com/openai/math (paper: preprints/Vanishing-of-higher-bounded-Hochschild-cohomology-September-23-2026/paper.pdf; Apache License 2.0); Lean declaration `OAI.BoundedHochschild.KadisonRingrose.exists_unital_completelyPositive_extension`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/BoundedHochschild/UnitalPositiveExtension.lean#L19

import Mathlib
import Definitions.Def_KadisonRingroseSupport2

namespace OAI

noncomputable section

open Filter Topology
open scoped ComplexOrder InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Nontrivial H]

theorem exists_unital_completelyPositive_extension
    (S : Submodule ℂ A) (h1 : (1 : A) ∈ S) (hstar : ∀ a ∈ S, star a ∈ S)
    (φ : S →ₗ[ℂ] (H →L[ℂ] H)) (hφ1 : φ ⟨1, h1⟩ = 1)
    (hφ : ∀ n (X : operatorSystemMatrices S n),
      0 ≤ (X : CStarMatrix (Fin n) (Fin n) A) →
        0 ≤ operatorSystemAmplification S φ n X) :
    ∃ Φ : CompletelyPositiveMap A (H →L[ℂ] H),
      Φ 1 = 1 ∧ (∀ a, ‖Φ a‖ ≤ ‖a‖) ∧ ∀ a : S, Φ (a : A) = φ a := by
  sorry

end BoundedHochschild.KadisonRingrose
end
end OAI
