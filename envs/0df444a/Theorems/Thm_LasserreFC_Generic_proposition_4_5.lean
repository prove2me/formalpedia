-- Prove2me | Theorems.Thm_LasserreFC_Generic_proposition_4_5
-- name    : LasserreFC.Generic.proposition_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:32:28.928515+00:00
-- url     : https://prove2.me/theorems/85c97e29-fdc1-4758-9c04-114d9d5d107b
-- title:
--   Proposition 4.5, p. 15 — under Condition 4.3, CQC, strict complementarity and SOSC hold at every local minimizer
-- statement:
--   Let $m_1\le n$ and let $(f,h,g)$ be admissible for the degrees $d_0$, $d_i$, $d'_j$. If Condition 4.3 holds, then at every local minimizer $u$ of (1.1),
--   $$\text{CQC holds at }u,\ \text{and there are multipliers }\lambda,\mu\text{ satisfying (1.3), (1.4), (1.5) and (1.7)}.$$
--   That is, the constraint qualification, strict complementarity and second order sufficiency conditions all hold at every local minimizer.
--
--   With the nonvanishing of the polynomials of Condition 4.3 on a nonempty Zariski open set, this gives Theorem 1.2.
--
--   **Formalization Note** Only the first sentence of Proposition 4.5 is posed; its items 1)–4) are restatements of Proposition 4.4 at local minimizers. The standing assumption $m_1\le n$ is Condition 4.3's own.
-- source:
--   J. Nie, Optimality conditions and finite convergence of Lasserre's hierarchy, arXiv:1206.0319v2, p. 15, Proposition 4.5 (first sentence)

import Mathlib
import Definitions.Def_LasserreFC_Generic_Setting
import Definitions.Def_LasserreFC_Generic_Cond43

namespace LasserreFC.Generic

open MvPolynomial

/-- Proposition 4.5, p. 15 (first sentence). Let `m₁ ≤ n` and `(f, h, g)` be admissible for
`(d₀, d, d')`. If Condition 4.3 holds, then the constraint qualification, strict complementarity
and second order sufficiency conditions all hold at every local minimizer of (1.1). -/
theorem proposition_4_5 {n m1 m2 : ℕ} (hm1 : m1 ≤ n) (P : POP n m1 m2) (d0 : ℕ)
    (d : Fin m1 → ℕ) (d' : Fin m2 → ℕ) (hadm : P.Admissible d0 d d')
    (hC : Cond43 P d0 d d') :
    ∀ u ∈ P.K, IsLocalMinOn (fun x => eval x P.f) P.K u → OptCond P u := by sorry

end LasserreFC.Generic
