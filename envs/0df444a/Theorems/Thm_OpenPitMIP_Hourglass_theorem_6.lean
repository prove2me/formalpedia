-- Prove2me | Theorems.Thm_OpenPitMIP_Hourglass_theorem_6
-- name    : OpenPitMIP.Hourglass.theorem_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:56:27.498739+00:00
-- url     : https://prove2.me/theorems/9fa746eb-bf18-4e49-aeb9-cc59c7543d9b
-- title:
--   Theorem 6, p. 1434 — simplified hourglass cut (q(S) + q_b − U) x_b ≤ ∑_{b′∈S∪{b}} q_{b′} y^W_{b′} is valid for MK
-- statement:
--   Let $G=(\mathcal B,\mathcal A)$ be a finite directed acyclic graph, $q_b>0$ for every $b$, and $U>0$, and let MK be the mode-knapsack set of (24)–(28), whose points are triples $(x,y^P,y^W)$. Let $b\in\mathcal B$ and let $S\subseteq cl(b)\setminus\{b\}$ be a set of predecessors of $b$ with $q(S)=\sum_{b'\in S}q_{b'}\ge U$. Then every point of MK satisfies
--   $$\bigl(q(S)+q_b-U\bigr)\,x_b\le\sum_{b'\in S\cup\{b\}}q_{b'}\,y^W_{b'} .$$
--
--   This is the single-period, single-block-cluster form of the hourglass cuts: once $b$ is started, its predecessors in $S$ must be fully extracted, and since their weight exceeds the processing capacity, a minimum amount must be sent to waste.
--
--   **Formalization Note** In MK, $b'\prec b$ means a directed path from $b$ to $b'$ in $G$.
-- source:
--   Oper. Res. 68(5), Theorem 6, p. 1434

import Mathlib
import Definitions.Def_OpenPitMIP_Hourglass_Setting

namespace OpenPitMIP.Hourglass

/-- Theorem 6 (simplified hourglass cuts), p. 1434. In the mode-knapsack set MK over a DAG
`G = (𝓑, 𝒜)` with positive weights `q` and capacity `U > 0`: for a block `b` and a set
`S ⊆ cl(b) \ {b}` of predecessors of `b` with `q(S) ≥ U`, the inequality
`(q(S) + q_b − U) x_b ≤ ∑_{b'∈S∪{b}} q_{b'} y^W_{b'}` is valid for MK. -/
theorem theorem_6 {B : Type} [Fintype B] [DecidableEq B]
    (A : B → B → Prop) (hA : ∀ b, ¬ Relation.TransGen A b b)
    (q : B → ℝ) (hq : ∀ b, 0 < q b) (U : ℝ) (hU : 0 < U)
    (b : B) (S : Finset B) (hS : S ⊆ mkCl A b \ {b}) (hqS : U ≤ ∑ b' ∈ S, q b') :
    ∀ v ∈ MK A q U,
      ((∑ b' ∈ S, q b') + q b - U) * v.1 b ≤ ∑ b' ∈ S ∪ {b}, q b' * v.2.2 b' := by sorry

end OpenPitMIP.Hourglass
