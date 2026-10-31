-- Prove2me | Theorems.Thm_GhostPenalty_lemma_1_i
-- name    : GhostPenalty.lemma_1_i
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:34:56.797919+00:00
-- url     : https://prove2.me/theorems/c3c2bd09-614c-4bb0-b91f-a85098085204
-- title:
--   Lemma 1 (i) — the CQ (13) and $N_{\alpha\mathbb B^n_\infty\cap(K-\hat x)}=N_{\alpha\mathbb B^n_\infty}+N_{K-\hat x}$
-- statement:
--   Let $K\subseteq\mathbb R^n$ be nonempty, closed and convex. For every $\hat x\in K$, every $\alpha>0$ and every $d\in\alpha\mathbb B^n_\infty\cap(K-\hat x)$, the constraint qualification
--   $$[-N_{\alpha\mathbb B^n_\infty}(d)]\cap N_{K-\hat x}(d)=\{0\} \tag{13}$$
--   holds, and
--   $$N_{\alpha\mathbb B^n_\infty\cap(K-\hat x)}(d)=N_{\alpha\mathbb B^n_\infty}(d)+N_{K-\hat x}(d).$$
--   The normal cone of the subproblem's set constraint therefore splits into the box part and the $K$ part.
--
--   **Formalization Note** $K-\hat x=\{u:\ \hat x+u\in K\}$; normal cones are the published `normalCone`, evaluated at $d$, which lies in each set; $-N$ and $N+N'$ are pointwise.
--
--   Differences from the source:
--   - encoding: classical normal cones N_K(x), N_{ℝᵐ₋}(y), empty off the set → published normalCone (defined everywhere) used only at points of the set, and negOrthantNormalCone with the feasibility clause built in; reason: same sets at every point where the source uses them
-- source:
--   Facchinei, Kungurtsev, Lampariello & Scutari, Ghost Penalties in Nonconvex Constrained Optimization, arXiv:1709.03384v3, Lemma 1 (i), (13), p.9

import Mathlib
import Definitions.Def_FirstOrderOpt_ConvexTheory_normalCone
import Definitions.Def_GhostPenalty_box
open FirstOrderOpt.ConvexTheory
open scoped Pointwise

namespace GhostPenalty

/-- **Lemma 1 (i): a constraint qualification and the normal cone of `αBⁿ∞ ∩ (K − x̂)`.**
Facchinei, Kungurtsev, Lampariello & Scutari, *Ghost Penalties in Nonconvex Constrained
Optimization*, arXiv:1709.03384v3, Lemma 1 (i), p.9: "For every `x̂ ∈ K`, and for every `α > 0` and
`d ∈ αBⁿ∞ ∩ (K − x̂)`, the constraint qualification `[−N_{αBⁿ∞}(d)] ∩ N_{K−x̂}(d) = {0}` (13)
holds and, in turn, `N_{αBⁿ∞∩(K−x̂)}(d) = N_{αBⁿ∞}(d) + N_{K−x̂}(d)`".

**Formalization Note.** `K` is closed and convex and contains `x̂`, hence nonempty (the blanket
assumption of (P), the only one Lemma 1 involves). `K − x̂` is `{u | x̂ + u ∈ K}`; normal cones are the published
`normalCone`, used at `d`, a point of each set; `−N` and `N + N'` are pointwise. -/
theorem lemma_1_i {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (hKcl : IsClosed K) (hKcv : Convex ℝ K) (xh : EuclideanSpace ℝ (Fin n)) (hxh : xh ∈ K)
    (α : ℝ) (hα : 0 < α) (d : EuclideanSpace ℝ (Fin n))
    (hd : d ∈ box n α ∩ {u | xh + u ∈ K}) :
    (-normalCone (box n α) d) ∩ normalCone {u | xh + u ∈ K} d = {0} ∧
      normalCone (box n α ∩ {u | xh + u ∈ K}) d =
        normalCone (box n α) d + normalCone {u | xh + u ∈ K} d := by sorry

end GhostPenalty
