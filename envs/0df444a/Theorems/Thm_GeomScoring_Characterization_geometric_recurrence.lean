-- Prove2me | Theorems.Thm_GeomScoring_Characterization_geometric_recurrence
-- name    : GeomScoring.Characterization.geometric_recurrence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:44:48.628006+00:00
-- url     : https://prove2.me/theorems/219fed21-e771-4c67-ae9f-8316190e419c
-- title:
--   §3, p. 7 — a strictly decreasing score vector whose first m−1 and last m−1 entries are affinely equivalent is geometric
-- statement:
--   Let $v_1>v_2>\dots>v_m$ be a strictly decreasing sequence of real numbers such that $v_1,\dots,v_{m-1}$ is affinely equivalent to $v_2,\dots,v_m$, i.e. there are $\alpha>0$ and $\beta$ with $v_j=\alpha v_{j+1}+\beta$ for $j=1,\dots,m-1$. Then there is a parameter $p>0$ such that $v$ is affinely equivalent to the geometric scores
--   $$g^m_j(p)=\begin{cases}p^{m-j} & 1<p,\\ m-j & p=1,\\ 1-p^{m-j} & 0<p<1,\end{cases}\qquad j=1,\dots,m.$$
--
--   This is the computation of §3 that turns the self-similarity of the score vector into the closed form of Definition 5: normalising the last two scores to $0$ and $1$, each further score is obtained from the previous ones by scaling with $p$ and adding $1$, so $s^m_j=(p^{m-j}-1)/(p-1)$ for $p\ne1$ and Borda for $p=1$.
--
--   **Formalization Note.** Positions are 0-based; the geometric scores are `geomScore p m` of the model file. The paper carries out the computation for $m\ge3$; the statement is given for every $m$, since for $m\le2$ every strictly decreasing vector is affinely equivalent to $g^m(p)$ for any $p>0$.
-- source:
--   Kondratev, Ianovski & Nesterov, How should we score athletes and candidates: geometric scoring rules, arXiv:1907.05082v5, §3, pp. 6–7, paragraph before Definition 5 ('Given that we need not distinguish scores up to scaling and translation …')

import Mathlib
import Definitions.Def_GeomScoring_Characterization_Model

namespace GeomScoring.Characterization

theorem geometric_recurrence (m : ℕ) (v : Fin m → ℝ) (hv : StrictAnti v)
    (h : AffEquiv (initSeg v (m - 1)) (finalSeg v (m - 1))) :
    ∃ p : ℝ, 0 < p ∧ AffEquiv v (geomScore p m) := by sorry

end GeomScoring.Characterization
