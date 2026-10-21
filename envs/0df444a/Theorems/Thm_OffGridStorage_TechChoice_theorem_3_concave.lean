-- Prove2me | Theorems.Thm_OffGridStorage_TechChoice_theorem_3_concave
-- name    : OffGridStorage.TechChoice.theorem_3_concave
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:43:56.747986+00:00
-- url     : https://prove2.me/theorems/50f33d84-939d-4d84-88ee-c708e3b40b7e
-- title:
--   Theorem 3, first sentence, p. 13 — the full-discharge objective is jointly concave over its domain Q ≥ 0, K ≥ 0
-- statement:
--   Under the standing assumptions, let $\Pi_F$ be the full-discharge expected profit of eq. (5),
--
--   $$\Pi_F(Q,K)=T\Bigl(g\,E\bigl[\min[q,D_H]+\min[e(q-D_H)^+,K]\bigr]-\frac{c_K}{e}K-c_QQ\Bigr),\qquad q\sim U[0,Q].$$
--
--   Then $(Q,K)\mapsto\Pi_F(Q,K)$ is jointly concave on its whole domain $\{(Q,K): Q\ge 0,\ K\ge 0\}$.
--
--   This is the concavity statement with which Theorem 3 opens; the paper proves it by signing the Hessian of the closed form (20), eqs. (21)–(22), and then finds the optimum from the first-order conditions.
--
--   **Formalization Note** The statement is about $\Pi_F$ itself (eq. (5), the expectation written as $q=Qv$ with $v$ uniform on $[0,1]$), not only about the closed form (20), which equals $\Pi_F$ only where $D_H+K/e\le Q$. The paper's "domain" is read as all plans $Q\ge 0$, $K\ge 0$. The hypotheses $c_Q>0$, $c_K\ge 0$, $T\ge 1$ of the standing assumptions are added relative to the page.
-- source:
--   Kaps, Marinesi & Netessine, When Should the Off-grid Sun Shine at Night?, SSRN 3761397 (version of May 11, 2023), p. 13, Theorem 3 (first sentence); proof pp. 37–38, Appendix A.3, eqs. (21)–(22)

import Mathlib
import Definitions.Def_OffGridStorage_TechChoice_Model

namespace OffGridStorage.TechChoice

/-- Theorem 3, first sentence, p. 13: the full-discharge objective `Π_F` of eq. (5) is jointly
concave in `(Q, K)` over its whole domain `{(Q, K) : Q ≥ 0, K ≥ 0}`. -/
theorem theorem_3_concave (p : Params) (hp : Standing p) :
    ConcaveOn ℝ {x : ℝ × ℝ | 0 ≤ x.1 ∧ 0 ≤ x.2}
      (fun x => profitF p x.1 x.2) := by sorry

end OffGridStorage.TechChoice
