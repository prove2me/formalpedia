-- Prove2me | Theorems.Thm_GeomScoring_Characterization_theorem_6
-- name    : GeomScoring.Characterization.theorem_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:45:07.519275+00:00
-- url     : https://prove2.me/theorems/7a46c617-1cfd-4903-8bc9-d6ef2c47101c
-- title:
--   Theorem 6, p. 7 — a scoring rule is independent of unanimous winners and losers iff it is a geometric scoring rule
-- statement:
--   Let $s$ be a scoring rule for $M$ potential athletes, where $M$ is finite or $M=\infty$. Then $s$ satisfies both independence of unanimous winners and independence of unanimous losers if and only if it is a geometric scoring rule: there is a single parameter $0<p<\infty$ such that for every number of athletes $m\le M$ the scores $s^m_1,\dots,s^m_m$ are affinely equivalent to
--   $$g^m_j(p)=\begin{cases}p^{m-j} & 1<p,\\ m-j & p=1,\\ 1-p^{m-j} & 0<p<1,\end{cases}\qquad j=1,\dots,m,$$
--   that is, $s^m_j=\alpha_m\,g^m_j(p)+\beta_m$ for some $\alpha_m>0$ and $\beta_m$.
--
--   This is the main characterisation of the paper. Each axiom alone is weak — any strictly decreasing score vector, truncated at the right end or the left end, satisfies one of them — but together they leave a one-parameter family: $p>1$ gives convex (geometric) scores, $p=1$ Borda's rule, and $0<p<1$ concave (inverse geometric) scores. Later results of the paper (Theorems 9 and 10) single out members of this family by adding further axioms.
--
--   **Formalization Note.** Positions are 0-based (Lean's `j` is the paper's $j+1$), and $M$ is an element of `ℕ∞`. The parameter is one $p$ for the whole rule, as in Definition 5, and strictly positive and finite: the limits $p\to\infty$ and $p\to0$ (generalised plurality and antiplurality) are multi-round generalised rules, not scoring rules. The axioms are those of the model file: strict "ranked first/last" and profiles with at least one race. For $M\le2$ both sides hold for exactly the rules with strictly decreasing scores, for every $p$.
-- source:
--   Kondratev, Ianovski & Nesterov, How should we score athletes and candidates: geometric scoring rules, arXiv:1907.05082v5, p. 7, Theorem 6 (with Definition 5, p. 7)

import Mathlib
import Definitions.Def_GeomScoring_Characterization_Model

namespace GeomScoring.Characterization

theorem theorem_6 (M : ℕ∞) (s : ScoringRule) :
    (IndepUnanimousWinners M s ∧ IndepUnanimousLosers M s) ↔
      ∃ p : ℝ, 0 < p ∧ ∀ m : ℕ, (m : ℕ∞) ≤ M → AffEquiv (s m) (geomScore p m) := by sorry

end GeomScoring.Characterization
