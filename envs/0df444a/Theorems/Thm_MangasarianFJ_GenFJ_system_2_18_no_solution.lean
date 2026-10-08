-- Prove2me | Theorems.Thm_MangasarianFJ_GenFJ_system_2_18_no_solution
-- name    : MangasarianFJ.GenFJ.system_2_18_no_solution
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:41:21.299069+00:00
-- url     : https://prove2.me/theorems/99c51668-56ee-4a79-821c-aa18ca68a51b
-- title:
--   §2, proof of the generalized Fritz John conditions, pp. 41–42 — (2.17) has the solution x̄ ∈ D and (2.18) has no solution in D
-- statement:
--   Let $\bar x$ be a solution of (1.1): $\bar x\in S$ and $\theta(\bar x)\le\theta(x)$ for all $x\in S$. Let $\bar M$ be the active set (2.13) and $D=\{x: g_i(x)<0,\ i\in M\setminus\bar M\}$ (2.14). With $f_1(x)=\theta(x)-\theta(\bar x)$ (2.15) and $f_i=g_{p_i}$, $p_i\in\bar M$ (2.16), the following hold:
--
--   1. $\bar x\in D$, and $\bar x$ solves (2.17): $g_i(\bar x)=0$ for $i\in\bar M$ and $h_j(\bar x)=0$ for $j\in K$ (and trivially $f_1(\bar x)=0$);
--   2. the system (2.18)
--   $$
--   \theta(x)-\theta(\bar x)<0,\qquad g_i(x)<0,\ i\in\bar M,\qquad h_j(x)=0,\ j\in K
--   $$
--   has no solution $x\in D$.
--
--   These are exactly the hypotheses (2.1)–(2.2) of Lemma 2 for the family $f_1,\dots,f_l$, which is how the main result follows from Lemma 2.
--
--   **Formalization Note** The family $f_1,\dots,f_l$ of (2.15)–(2.16) is substituted, not defined: the statement lists the conditions on $\theta$ and on $g_i$, $i\in\bar M$, directly, so no enumeration $p_i$ of $\bar M$ is needed. The trivial clause $f_1(\bar x)=\theta(\bar x)-\theta(\bar x)=0$ is omitted. No differentiability is used in this step, so the $C^1$ hypothesis of §1 is dropped (a stronger statement).
-- source:
--   Mangasarian and Fromovitz, The Fritz John necessary optimality conditions in the presence of equality and inequality constraints, J. Math. Anal. Appl. 17 (1967), pp. 41–42, §2, proof of the generalized Fritz John conditions, (2.15)–(2.19)

import Mathlib
import Definitions.Def_MangasarianFJ_GenFJ_Setting

namespace MangasarianFJ.GenFJ
theorem system_2_18_no_solution {n m k : ℕ} (θ : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : Fin m → EuclideanSpace ℝ (Fin n) → ℝ) (h : Fin k → EuclideanSpace ℝ (Fin n) → ℝ)
    (xbar : EuclideanSpace ℝ (Fin n)) (hsol : IsSolution θ g h xbar) :
    xbar ∈ region g xbar ∧
    ((∀ i ∈ activeSet g xbar, g i xbar = 0) ∧ ∀ j, h j xbar = 0) ∧
    ¬ ∃ x ∈ region g xbar,
      θ x - θ xbar < 0 ∧ (∀ i ∈ activeSet g xbar, g i x < 0) ∧ ∀ j, h j x = 0 := by sorry
end MangasarianFJ.GenFJ
