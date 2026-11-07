-- Prove2me | Theorems.Thm_KSATWindow_theorem_1_1
-- name    : KSATWindow.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:33:09.87421+00:00
-- url     : https://prove2.me/theorems/b189ee1c-ff00-4643-bb10-77dfaa165cba
-- title:
--   Theorem 1.1 — the scaling window of random $k$-SAT is $\tilde W_\eta(n)=O_{k,\eta}(n^{1/2+1/k})$
-- statement:
--   For every fixed $k\ge3$ and $\eta\in(0,1/2)$,
--   $$\tilde W_\eta(n)=O_{k,\eta}\big(n^{1/2+1/k}\big)\qquad(n\to\infty),$$
--   where $\tilde W_\eta(n)=\tilde m_{1-\eta}(n)-\tilde m_\eta(n)$ and $\tilde m_u(n)$ is the least $m$ for which the conjunction of $m$ independent uniform signed $k$-clauses on $n$ variables is unsatisfiable with probability at least $u$.
--
--   Since $1/2+1/k<1$, this is a polynomial improvement over the earlier $O(n/\log n)$, and it meets the hypothesis of the Abbe–Montanari criterion, which yields the satisfiability conjecture.
--
--   **Formalization Note** The window is a real number built from natural-number quantiles; $O$ is `Asymptotics.IsBigO` along $n\to\infty$ in $\mathbb N$, with $k$ and $\eta$ fixed before the constant.
--
--   Differences from the source:
--   - encoding: W̃_η(n) = m̃_{1−η}(n) − m̃_η(n) → the real difference of two ℕ-valued sInf quantiles; reason: m̃_u(n) is a least natural number; its set is nonempty for n ≥ k, u < 1
-- source:
--   Carenini, A polynomial scaling window for random k-SAT and a proof of the satisfiability conjecture, STOC 2027 submission (manuscript sha256 1664cf10…), §1, p.2, Theorem 1.1

import Mathlib
import Definitions.Def_SATVariance
import Definitions.Def_KSATWindow_Window
open MeasureTheory ProbabilityTheory OAI.RandomKSAT

namespace KSATWindow

/-- **Theorem 1.1, p.2 — the scaling window of random k-SAT.** G. Carenini, *A polynomial scaling window for random k-SAT and a proof of the satisfiability
conjecture*, STOC 2027 submission (manuscript sha256 1664cf10…), §1, p.2.

For every fixed `k ≥ 3` and `η ∈ (0, 1/2)`, `W̃_η(n) = O_{k,η}(n^{1/2+1/k})`, where
`W̃_η(n) = m̃_{1−η}(n) − m̃_η(n)` and `m̃_u(n)` is the least `m` with
`P(F_{n,m} is unsatisfiable) ≥ u`.

**Formalization Note.** `O` as `n → ∞` along `ℕ` (`Asymptotics.IsBigO` at `atTop`), with `k` and
`η` fixed before the constant. `n^{1/2+1/k}` is a real power. -/
theorem theorem_1_1 (k : ℕ) (hk : 3 ≤ k) (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1 / 2) :
    (fun n : ℕ => window n k η) =O[Filter.atTop]
      fun n : ℕ => (n : ℝ) ^ ((1 : ℝ) / 2 + 1 / (k : ℝ)) := by sorry

end KSATWindow
