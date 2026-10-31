-- Prove2me | Theorems.Thm_GhostPenalty_lemma_1_ii
-- name    : GhostPenalty.lemma_1_ii
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:34:57.742797+00:00
-- url     : https://prove2.me/theorems/6cb5cca2-cad6-47a4-8581-786b77271604
-- title:
--   Lemma 1 (ii) — $x\mapsto\alpha\mathbb B^n_\infty\cap(K-x)$ is continuous on $K$ relative to $K$
-- statement:
--   Let $K\subseteq\mathbb R^n$ be nonempty, closed and convex. For every $\alpha>0$, the set-valued map
--   $$x\ \mapsto\ \alpha\mathbb B^n_\infty\cap(K-x)$$
--   is continuous on $K$ relative to $K$: at every $\bar x\in K$ it is outer and inner semicontinuous relative to $K$.
--
--   Differences from the source:
--   - encoding: continuity of a set-valued mapping (Rockafellar–Wets) → outer and inner semicontinuity in sequential form (OuterSemicontWithinAt ∧ InnerSemicontWithinAt) at every x̄ ∈ K; reason: the sequential form is Rockafellar–Wets' definition in ℝⁿ
-- source:
--   Facchinei, Kungurtsev, Lampariello & Scutari, Ghost Penalties in Nonconvex Constrained Optimization, arXiv:1709.03384v3, Lemma 1 (ii), p.9

import Mathlib
import Definitions.Def_GhostPenalty_box
import Definitions.Def_GhostPenalty_OuterSemicontWithinAt
import Definitions.Def_GhostPenalty_InnerSemicontWithinAt

namespace GhostPenalty

/-- **Lemma 1 (ii): continuity of `x ↦ αBⁿ∞ ∩ (K − x)`.**
Facchinei, Kungurtsev, Lampariello & Scutari, *Ghost Penalties in Nonconvex Constrained
Optimization*, arXiv:1709.03384v3, Lemma 1 (ii), p.9: "for every `α > 0`, the set-valued mapping `αBⁿ∞ ∩ (K − •)` is
continuous on `K` relative to `K`".

**Formalization Note.** `K` is nonempty, closed and convex (blanket assumption). "Continuous at
`x̄` relative to `K`" is outer and inner semicontinuity at `x̄` relative to `K` (Rockafellar &
Wets, Def. 5.4), in the sequential form of `OuterSemicontWithinAt` and `InnerSemicontWithinAt`;
"on `K`" is "at every `x̄ ∈ K`". -/
theorem lemma_1_ii {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hKne : K.Nonempty)
    (hKcl : IsClosed K) (hKcv : Convex ℝ K) (α : ℝ) (hα : 0 < α) :
    ∀ xbar ∈ K,
      OuterSemicontWithinAt (fun x => box n α ∩ {u | x + u ∈ K}) K xbar ∧
        InnerSemicontWithinAt (fun x => box n α ∩ {u | x + u ∈ K}) K xbar := by sorry

end GhostPenalty
