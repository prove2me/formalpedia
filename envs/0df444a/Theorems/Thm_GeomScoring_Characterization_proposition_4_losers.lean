-- Prove2me | Theorems.Thm_GeomScoring_Characterization_proposition_4_losers
-- name    : GeomScoring.Characterization.proposition_4_losers
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:44:30.547425+00:00
-- url     : https://prove2.me/theorems/9fcfbed3-3c85-41b9-bc60-9cbfe5dbf666
-- title:
--   Proposition 4 (first part), p. 6 — independence of unanimous losers iff decreasing scores whose shorter vectors are prefixes up to affine maps
-- statement:
--   Let $s$ be a scoring rule for $M$ potential athletes ($M$ finite or $\infty$). Then $s$ satisfies independence of unanimous losers if and only if the following two conditions hold:
--
--   1. for every $m\le M$ the scores are strictly decreasing, $s^m_1>s^m_2>\dots>s^m_m$;
--   2. for all $k<m\le M$, the scores for $k$ athletes are affinely equivalent to the first $k$ scores for $m$ athletes: there are $\alpha>0$ and $\beta$ with
--   $$s^k_j=\alpha\,s^m_j+\beta\qquad(j=1,\dots,k).$$
--
--   In words, dropping athletes who always finish last never changes the ranking of the others exactly when the score vector for fewer athletes is obtained, up to scaling and translation, by truncating the longer vector. This is the first half of the characterisation behind Theorem 6.
--
--   **Formalization Note.** Positions are 0-based (Lean's `j` is the paper's $j+1$). Independence of unanimous losers is the predicate `IndepUnanimousLosers M s` of the model file: strict "ranked last" and profiles with at least one race; the athlete sets are arbitrary finite types of size at most $M$.
-- source:
--   Kondratev, Ianovski & Nesterov, How should we score athletes and candidates: geometric scoring rules, arXiv:1907.05082v5, p. 6, Proposition 4 (first paragraph); proof pp. 24–25

import Mathlib
import Definitions.Def_GeomScoring_Characterization_Model

namespace GeomScoring.Characterization

theorem proposition_4_losers (M : ℕ∞) (s : ScoringRule) :
    IndepUnanimousLosers M s ↔
      (∀ m : ℕ, (m : ℕ∞) ≤ M → StrictAnti (s m)) ∧
        ∀ k m : ℕ, k < m → (m : ℕ∞) ≤ M → AffEquiv (s k) (initSeg (s m) k) := by sorry

end GeomScoring.Characterization
