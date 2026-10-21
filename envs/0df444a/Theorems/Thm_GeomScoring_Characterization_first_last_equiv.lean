-- Prove2me | Theorems.Thm_GeomScoring_Characterization_first_last_equiv
-- name    : GeomScoring.Characterization.first_last_equiv
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:44:54.956236+00:00
-- url     : https://prove2.me/theorems/485adf97-99e0-436e-87b0-c18649b8dbfe
-- title:
--   §3, p. 6 — under both independence axioms the first and last k scores for m athletes are affinely equivalent
-- statement:
--   Let $s$ be a scoring rule for $M$ potential athletes that satisfies both independence of unanimous winners and independence of unanimous losers. Then for all $k<m\le M$ the first $k$ scores and the last $k$ scores for $m$ athletes are affinely equivalent: there are $\alpha>0$ and $\beta$ with
--   $$s^m_j=\alpha\,s^m_{m-k+j}+\beta\qquad(j=1,\dots,k).$$
--   In particular ($k=m-1$), $s^m_1,\dots,s^m_{m-1}$ is affinely equivalent to $s^m_2,\dots,s^m_m$.
--
--   This is the step of §3 that combines the two halves of Proposition 4: the scores for $k$ athletes are affinely equivalent both to the first and to the last $k$ scores for $m$ athletes, and affine equivalence is an equivalence relation. The case $k=m-1$ is what forces the geometric form.
--
--   **Formalization Note.** Positions are 0-based. The statement is given for every $k<m$, as in the paper's sentence; its "in particular" case is $k=m-1$.
-- source:
--   Kondratev, Ianovski & Nesterov, How should we score athletes and candidates: geometric scoring rules, arXiv:1907.05082v5, §3, p. 6, paragraph after Proposition 4 ('The property of affine equivalence is clearly an equivalence relation, …')

import Mathlib
import Definitions.Def_GeomScoring_Characterization_Model

namespace GeomScoring.Characterization

theorem first_last_equiv (M : ℕ∞) (s : ScoringRule)
    (hW : IndepUnanimousWinners M s) (hL : IndepUnanimousLosers M s) :
    ∀ k m : ℕ, k < m → (m : ℕ∞) ≤ M → AffEquiv (initSeg (s m) k) (finalSeg (s m) k) := by sorry

end GeomScoring.Characterization
