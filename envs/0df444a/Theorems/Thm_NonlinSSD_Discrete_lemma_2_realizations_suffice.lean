-- Prove2me | Theorems.Thm_NonlinSSD_Discrete_lemma_2_realizations_suffice
-- name    : NonlinSSD.Discrete.lemma_2_realizations_suffice
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T21:02:59.110277+00:00
-- url     : https://prove2.me/theorems/8238a9f4-201a-45ff-8e7d-f0cf96de436d
-- title:
--   Lemma 2 — for finite distributions, second-order dominance need only be checked at the realizations of Y_i
-- statement:
--   Let $p_1,\dots,p_n \ge 0$ with $\sum_j p_j = 1$ be scenario probabilities, and for $i = 1,\dots,m$ let $x_{i1},\dots,x_{in}$ and $y_{i1},\dots,y_{in}$ be the realizations of random variables $X_i$ and $Y_i$, and let $[a_i,b_i]$ be intervals with $a_i \le y_{ij} \le b_i$ for all $i, j$. Then the dominance constraints on the intervals,
--   $$\sum_{j=1}^n p_j (\eta - x_{ij})_+ \le \sum_{j=1}^n p_j (\eta - y_{ij})_+ \quad \text{for all } \eta \in [a_i,b_i],\ i \in I, \tag{36}$$
--   are equivalent to the finitely many inequalities
--   $$\sum_{j=1}^n p_j (y_{ik} - x_{ij})_+ \le \sum_{j=1}^n p_j (y_{ik} - y_{ij})_+, \quad i \in I,\ k \in J. \tag{37}$$
--   Moreover, (37) is equivalent to the same inequality for **all** $\eta \in \mathbb R$, i.e. to second-order stochastic dominance of $X_i$ over $Y_i$ on the whole line.
--
--   Since $F_2(X_i;\eta) = \sum_j p_j(\eta - x_{ij})_+$ for a finite distribution, the lemma turns the continuum of dominance constraints into the $mn$ constraints (39) of the nonlinear program (38)–(41).
--
--   **Formalization Note.** The second conjunct is the remark printed right after the proof ("In fact, we have proved that inequalities (37) are equivalent to (36) for arbitrary $[a_i,b_i]$ covering the realizations of $Y_i$. Thus, they are equivalent to the dominance relation enforced on the entire real line."). Positive parts are `max t 0`; (37) is the definition `DominanceConstraints`.
-- source:
--   Dentcheva, Ruszczyński, Optimality and duality theory for stochastic optimization problems with nonlinear dominance constraints, author manuscript (rev. April 2003; Math. Program. 2004, DOI 10.1007/s10107-003-0453-z), p. 15, Lemma 2 with Eqs. (36)–(37), and p. 16, remark after the proof

import Mathlib
import Definitions.Def_NonlinSSD_Discrete_Problem

open Finset

namespace NonlinSSD.Discrete

theorem lemma_2_realizations_suffice {m n : ℕ} (p : Fin n → ℝ) (hp0 : ∀ j, 0 ≤ p j)
    (hp1 : ∑ j, p j = 1) (a b : Fin m → ℝ) (y X : Fin m → Fin n → ℝ)
    (hab : ∀ i j, a i ≤ y i j ∧ y i j ≤ b i) :
    ((∀ i, ∀ η ∈ Set.Icc (a i) (b i),
        ∑ j, p j * max (η - X i j) 0 ≤ ∑ j, p j * max (η - y i j) 0) ↔
      DominanceConstraints p y X) ∧
    (DominanceConstraints p y X ↔
      ∀ i, ∀ η : ℝ, ∑ j, p j * max (η - X i j) 0 ≤ ∑ j, p j * max (η - y i j) 0) := by sorry

end NonlinSSD.Discrete
