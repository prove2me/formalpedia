-- Prove2me | Theorems.Thm_LowRankIndicator_proposition_1
-- name    : LowRankIndicator.proposition_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:18:04.797963+00:00
-- url     : https://prove2.me/theorems/c1539a0f-c29c-49f1-87ca-b30be47cb874
-- title:
--   Proposition 1 — a closed convex set is the closed convex hull of $S$ iff their support functions agree
-- statement:
--   Let $S$ be a subset of a real normed space $E$ and let $T\subseteq E$ be closed and convex. Write $\delta^*(\varphi;S)=\sup_{x\in S}\varphi(x)$ for the support function of $S$ at a continuous linear functional $\varphi$, with values in $[-\infty,+\infty]$. Then
--
--   $$T=\operatorname{cl}\operatorname{conv}(S)\quad\Longleftrightarrow\quad \delta^*(\varphi;T)=\delta^*(\varphi;S)\ \text{ for every }\varphi .$$
--
--   This is the classical one-to-one correspondence between closed convex sets and support functions; the main theorem of the paper reduces to it, comparing the support functions of two sets.
--
--   **Formalization Note** The support function may be $+\infty$, and it is $-\infty$ on the empty set; $S$ is allowed to be empty.
--
--   Differences from the source:
--   - generalization: Euclidean space → any real normed space `E : Type`; reason: the statement specializes to Euclidean space, which is such a space
--   - encoding: δ∗(α; S) = max_{x∈S} α⊤x → `EReal`-valued supremum over `S` of a continuous linear functional φ, `VectorSpaceOpt_support_functional`; reason: on a Euclidean space every continuous linear functional is α⊤·, and the supremum may be infinite
-- source:
--   Han & Gómez, Compact Extended Formulations for Low-Rank Functions with Indicator Variables, arXiv:2110.14884v2, Proposition 1, p.5 (support function, pp.4–5).

import Mathlib
import Definitions.Def_VectorSpaceOpt_support_functional

namespace LowRankIndicator

/-- **Proposition 1**, Han & Gómez, arXiv:2110.14884v2, p.5: "Given a set S and a closed convex set
T, T = cl conv(S) if and only if δ∗(·; T) = δ∗(·; S)."

**Formalization Note.** The paper's support function `δ∗(α; S) = max_{x∈S} α⊤x` (pp.4–5) is the
`EReal`-valued supremum `VectorSpaceOpt_support_functional S φ`, which is `⊤` when unbounded and
`⊥` on the empty set. `α` is a continuous linear functional `φ`. The paper's Euclidean space is any
real normed space `E`. `S` may be empty. -/
theorem proposition_1 {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (S T : Set E)
    (hTclosed : IsClosed T) (hTconvex : Convex ℝ T) :
    T = closure (convexHull ℝ S) ↔
      ∀ φ : E →L[ℝ] ℝ,
        VectorSpaceOpt_support_functional T φ = VectorSpaceOpt_support_functional S φ := by sorry

end LowRankIndicator
