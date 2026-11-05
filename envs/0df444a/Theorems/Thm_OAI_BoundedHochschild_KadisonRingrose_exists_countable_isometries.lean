-- Prove2me | Theorems.Thm_OAI_BoundedHochschild_KadisonRingrose_exists_countable_isometries
-- name    : OAI.BoundedHochschild.KadisonRingrose.exists_countable_isometries
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T14:42:22.781202+00:00
-- url     : https://prove2.me/theorems/c0217583-843a-4b73-a226-aac9e0a3eea2
-- title:
--   Countably many orthogonal isometries summing to one in the properly infinite case
-- statement:
--   Throughout, $M$ is a unital C*-algebra with a partial order making it star-ordered, $X$ is a complex Banach space, and $e:X^*\to M$ is an isometric conjugate-linear isomorphism, so $M$ is a von Neumann algebra with predual $X$ (the Lean hypothesis `e`). A family $(a_i)$ converges in the predual sense to $b$ (`PredualTendsto`) when $e^{-1}(a_i)(z)\to e^{-1}(b)(z)$ for every $z\in X$. The hypothesis `NoFiniteCentralSummand M` says that a central projection $p$ whose corner $pMp$ is finite (every isometry of the corner is unitary) must vanish. A partial isometry (`PartialIso`) is an element $v$ with $vv^*v=v$; its initial and final projections are $v^*v$ and $vv^*$. If $M$ has no finite central summand, there is a sequence $c_0,c_1,\dots$ of partial isometries with $c_i^*c_i=1$, with $(c_ic_i^*)(c_jc_j^*)=0$ for $i\ne j$, and with
--
--   $$\sum_{i\in s}c_ic_i^*\longrightarrow1\qquad(s\subset\mathbb N\text{ finite})$$
--
--   in the predual sense.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with the listed `Definitions` imported in place of the upstream modules; the definitions are supporting code for this statement. Only the keyword `lemma`, where used upstream, becomes `theorem`, and a leading `include ... in` or `omit ... in` moves to the preamble. It is a step of the Lean proof of the vanishing of higher bounded Hochschild cohomology.
-- source:
--   OpenAI, Vanishing of higher bounded Hochschild cohomology, September 23, 2026, https://github.com/openai/math (paper: preprints/Vanishing-of-higher-bounded-Hochschild-cohomology-September-23-2026/paper.pdf; Apache License 2.0); Lean declaration `OAI.BoundedHochschild.KadisonRingrose.exists_countable_isometries`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/BoundedHochschild/InfiniteMatrixColumns.lean#L125

import Mathlib
import Definitions.Def_KadisonRingroseSupport2

namespace OAI

noncomputable section

open Filter

namespace BoundedHochschild.KadisonRingrose

open HochschildComparison

universe u

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

theorem exists_countable_isometries (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (hno : NoFiniteCentralSummand M) :
    ∃ c : ℕ → PartialIso M, (∀ i, (c i).initial = 1) ∧
      (∀ i j, i ≠ j → (c i).final * (c j).final = 0) ∧
      PredualTendsto e (fun s : Finset ℕ => ∑ i ∈ s, (c i).final) atTop 1 := by
  sorry

end BoundedHochschild.KadisonRingrose
end
end OAI
