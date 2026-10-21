-- Prove2me | Theorems.Thm_GeomScoring_Characterization_proposition_4_winners
-- name    : GeomScoring.Characterization.proposition_4_winners
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:44:40.865362+00:00
-- url     : https://prove2.me/theorems/9850eb24-bce4-448d-81d1-45d3a639cba0
-- title:
--   Proposition 4 (second part), p. 6 — independence of unanimous winners iff decreasing scores whose shorter vectors are suffixes up to affine maps
-- statement:
--   Let $s$ be a scoring rule for $M$ potential athletes ($M$ finite or $\infty$). Then $s$ satisfies independence of unanimous winners if and only if the following two conditions hold:
--
--   1. for every $m\le M$ the scores are strictly decreasing, $s^m_1>s^m_2>\dots>s^m_m$;
--   2. for all $k<m\le M$, the scores for $k$ athletes are affinely equivalent to the last $k$ scores for $m$ athletes: there are $\alpha>0$ and $\beta$ with
--   $$s^k_j=\alpha\,s^m_{m-k+j}+\beta\qquad(j=1,\dots,k).$$
--
--   In words, dropping athletes who always finish first never changes the ranking of the others exactly when the score vector for fewer athletes is, up to scaling and translation, the tail of the longer vector. Together with the first part this yields Theorem 6.
--
--   **Formalization Note.** Positions are 0-based (Lean's `j` is the paper's $j+1$); the last $k$ entries of a length-$m$ vector are its Lean entries $m-k,\dots,m-1$. Independence of unanimous winners is the predicate `IndepUnanimousWinners M s` of the model file: strict "ranked first" and profiles with at least one race.
-- source:
--   Kondratev, Ianovski & Nesterov, How should we score athletes and candidates: geometric scoring rules, arXiv:1907.05082v5, p. 6, Proposition 4 (second paragraph); proof p. 25 ('The argument for independence of unanimous winners is analogous')

import Mathlib
import Definitions.Def_GeomScoring_Characterization_Model

namespace GeomScoring.Characterization

theorem proposition_4_winners (M : ℕ∞) (s : ScoringRule) :
    IndepUnanimousWinners M s ↔
      (∀ m : ℕ, (m : ℕ∞) ≤ M → StrictAnti (s m)) ∧
        ∀ k m : ℕ, k < m → (m : ℕ∞) ≤ M → AffEquiv (s k) (finalSeg (s m) k) := by sorry

end GeomScoring.Characterization
