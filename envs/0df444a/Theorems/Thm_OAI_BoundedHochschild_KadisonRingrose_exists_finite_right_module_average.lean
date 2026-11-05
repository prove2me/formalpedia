-- Prove2me | Theorems.Thm_OAI_BoundedHochschild_KadisonRingrose_exists_finite_right_module_average
-- name    : OAI.BoundedHochschild.KadisonRingrose.exists_finite_right_module_average
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T14:41:59.211818+00:00
-- url     : https://prove2.me/theorems/4bede555-1e27-4c50-a91c-a5ea1febc9c3
-- title:
--   A simultaneous right-module average of a finite family of completely bounded maps
-- statement:
--   Throughout, $M$ is a unital C*-algebra with a partial order making it star-ordered, $X$ is a complex Banach space, and $e:X^*\to M$ is an isometric conjugate-linear isomorphism, so $M$ is a von Neumann algebra with predual $X$ (the Lean hypothesis `e`). A family $(a_i)$ converges in the predual sense to $b$ (`PredualTendsto`) when $e^{-1}(a_i)(z)\to e^{-1}(b)(z)$ for every $z\in X$. The hypothesis `NoFiniteCentralSummand M` says that a central projection $p$ whose corner $pMp$ is finite (every isometry of the corner is unitary) must vanish. Let $M$ be nontrivial with no finite central summand, and let $T_0,\dots,T_n:M\to M$ be bounded linear maps with complete bounds $C_i$. Then there are bounded maps $S_i$ with $\|S_i\|\le C_i$ and $S_i(ab)=S_i(a)b$ for all $a,b$, such that the family $(S_i)$ lies in the weak closure of the simultaneous averages $\bigl(a\mapsto\sum_jT_i(am_j)m_j^*\bigr)_i$ over finite $(m_j)$ with $\sum_jm_jm_j^*=1$ (`weakFamilyAverageOrbit`).
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with the listed `Definitions` imported in place of the upstream modules; the definitions are supporting code for this statement. Only the keyword `lemma`, where used upstream, becomes `theorem`, and a leading `include ... in` or `omit ... in` moves to the preamble. It is a step of the Lean proof of the vanishing of higher bounded Hochschild cohomology.
-- source:
--   OpenAI, Vanishing of higher bounded Hochschild cohomology, September 23, 2026, https://github.com/openai/math (paper: preprints/Vanishing-of-higher-bounded-Hochschild-cohomology-September-23-2026/paper.pdf; Apache License 2.0); Lean declaration `OAI.BoundedHochschild.KadisonRingrose.exists_finite_right_module_average`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/BoundedHochschild/FiniteModuleAverages.lean#L30

import Mathlib
import Definitions.Def_KadisonRingroseSupport2

namespace OAI

noncomputable section

open Topology

namespace BoundedHochschild.KadisonRingrose

open HochschildComparison

universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

theorem exists_finite_right_module_average [Nontrivial M]
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (hno : NoFiniteCentralSummand M)
    {n : ℕ} (T : Fin (n+1) → M →L[ℂ] M) (C : Fin (n+1) → ℝ)
    (hT : ∀ i, CompletelyBoundedEstimate (T i) (C i)) :
    ∃ S : Fin (n+1) → M →L[ℂ] M,
      (∀ i, ‖S i‖ ≤ C i ∧ ∀ a b, S i (a*b) = S i a * b) ∧
      (fun i => weakOperatorImage e (S i)) ∈ weakFamilyAverageOrbit e T := by
  sorry

end BoundedHochschild.KadisonRingrose
end
end OAI
