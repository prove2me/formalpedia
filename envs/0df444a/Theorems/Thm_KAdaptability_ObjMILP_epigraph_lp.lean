-- Prove2me | Theorems.Thm_KAdaptability_ObjMILP_epigraph_lp
-- name    : KAdaptability.ObjMILP.epigraph_lp
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:02:17.003163+00:00
-- url     : https://prove2.me/theorems/7bcf7cc0-ef88-4248-b899-44bb3cb1314e
-- title:
--   Proof of Theorem 2 — the objective of 𝒫𝒪_K is the optimal value of an epigraph LP
-- statement:
--   Let the uncertainty set $\Xi=\{\xi\in\mathbb R^Q: A\xi\le b\}$ be nonempty and bounded, let $K\ge1$, and fix any $x\in\mathbb R^N$ and $y^1,\dots,y^K\in\mathbb R^M$. Then the objective of the K-adaptability problem equals the optimal value of the epigraph LP:
--   $$\max_{\xi\in\Xi}\Big[\xi^\top Cx+\min_{k\in\mathcal K}\xi^\top Qy^k\Big]=\sup\Big\{\xi^\top Cx+\tau:\ \xi\in\mathbb R^Q,\ \tau\in\mathbb R,\ A\xi\le b,\ \tau\le\xi^\top Qy^k\ \forall k\in\mathcal K\Big\}.$$
--
--   This is the first step of the proof of Theorem 2: the inner minimum over the $K$ policies is replaced by an epigraph variable $\tau$, so that evaluating the objective becomes a linear program.
--
--   **Formalization Note** Both sides are extended reals (`EReal`). The policies are arbitrary real vectors; neither membership in $\mathcal Y$ nor the constraint $Tx+Wy^k\le h$ is needed.
-- source:
--   Hanasusanto, Kuhn, Wiesemann, K-Adaptability in Two-Stage Robust Binary Programming, preprint, Optimization Online 2014/03/4294 (revision of 2015-03-30), p. ec3 (PDF p. 37), Proof of Theorem 2, epigraph formulation

import Mathlib
import Definitions.Def_KAdaptability_ObjMILP_Problem
import Definitions.Def_KAdaptability_ObjMILP_POK
import Definitions.Def_KAdaptability_ObjMILP_EvalLPs

open Matrix

namespace KAdaptability.ObjMILP

/-- Proof of Theorem 2, p. ec3: for fixed `x` and `y¹, …, y^K` (`K ≥ 1`), the objective of 𝒫𝒪_K
equals the optimal value of the epigraph LP `max {ξ⊤Cx + τ : Aξ ≤ b, τ ≤ ξ⊤Qy^k ∀k}`. -/
theorem epigraph_lp {N M L nQ R : ℕ} (P : Problem N M L nQ R) (K : ℕ) (hK : 0 < K)
    (x : Fin N → ℝ) (ys : Fin K → Fin M → ℝ) :
    P.objPOK K x ys = P.epiValue K x ys := by sorry

end KAdaptability.ObjMILP
