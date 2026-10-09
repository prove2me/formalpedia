-- Prove2me | Theorems.Thm_OpenPitMIP_Hourglass_lifted_hourglass_MK
-- name    : OpenPitMIP.Hourglass.lifted_hourglass_MK
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:57:27.926273+00:00
-- url     : https://prove2.me/theorems/c655966a-5085-482d-abb0-6a9ce6c28a1d
-- title:
--   §5.2.1, p. 1434 — the lifted hourglass inequality (q(S) + q_b − U) x_b + ∑_{b′∈rcl(b)∖{b}} q_{b′} y^P_{b′} ≤ ∑_{b′∈S∪{b}} q_{b′} y^W_{b′} on MK
-- statement:
--   Under the hypotheses of Theorem 6 — $G=(\mathcal B,\mathcal A)$ a finite directed acyclic graph, $q>0$, $U>0$, $b\in\mathcal B$, and $S\subseteq cl(b)\setminus\{b\}$ with $q(S)\ge U$ — every point $(x,y^P,y^W)$ of MK satisfies the lifted inequality
--   $$\bigl(q(S)+q_b-U\bigr)\,x_b+\sum_{b'\in rcl(b)\setminus\{b\}}q_{b'}\,y^P_{b'}\le\sum_{b'\in S\cup\{b\}}q_{b'}\,y^W_{b'} ,$$
--   where $rcl(b)\setminus\{b\}$ is the set of successors of $b$.
--
--   The inequality involves blocks before $b$ (in $S$) and after $b$ (in $rcl(b)$), which is why the family is called the hourglass cuts.
--
--   **Formalization Note** $rcl(b)\setminus\{b\}$ is the set of $b'$ such that $G$ has a directed path from $b'$ to $b$.
-- source:
--   Oper. Res. 68(5), §5.2.1, unnumbered display after the proof of Theorem 6, p. 1434

import Mathlib
import Definitions.Def_OpenPitMIP_Hourglass_Setting

namespace OpenPitMIP.Hourglass

/-- The lifted hourglass inequality on MK, p. 1434 (displayed after the proof of Theorem 6). Under the
hypotheses of Theorem 6, the inequality
`(q(S) + q_b − U) x_b + ∑_{b'∈rcl(b)\{b}} q_{b'} y^P_{b'} ≤ ∑_{b'∈S∪{b}} q_{b'} y^W_{b'}`
is valid for MK. -/
theorem lifted_hourglass_MK {B : Type} [Fintype B] [DecidableEq B]
    (A : B → B → Prop) (hA : ∀ b, ¬ Relation.TransGen A b b)
    (q : B → ℝ) (hq : ∀ b, 0 < q b) (U : ℝ) (hU : 0 < U)
    (b : B) (S : Finset B) (hS : S ⊆ mkCl A b \ {b}) (hqS : U ≤ ∑ b' ∈ S, q b') :
    ∀ v ∈ MK A q U,
      ((∑ b' ∈ S, q b') + q b - U) * v.1 b + ∑ b' ∈ mkRcl A b \ {b}, q b' * v.2.1 b'
        ≤ ∑ b' ∈ S ∪ {b}, q b' * v.2.2 b' := by sorry

end OpenPitMIP.Hourglass
