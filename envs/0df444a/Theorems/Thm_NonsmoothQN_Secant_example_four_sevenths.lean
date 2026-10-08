-- Prove2me | Theorems.Thm_NonsmoothQN_Secant_example_four_sevenths
-- name    : NonsmoothQN.Secant.example_four_sevenths
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:24:13.09886+00:00
-- url     : https://prove2.me/theorems/77667fa9-57b9-44b6-8711-b7e7507c9c1b
-- title:
--   §5.1, p. 153 — the secant method from $x_0=4/7$
-- statement:
--   The number $4/7$ has the alternating binary expansion
--   $$\frac47=1-\frac12+\frac18-\frac1{16}+\cdots=\sum_{r=0}^{\infty}\left(2^{-3r}-2^{-3r-1}\right).$$
--   Run the secant method on $|x|$ with the inexact line search of §5.1 from $x_0=4/7$ and $H_0=1$. Then every line search terminates, and:
--   1. the first line search takes one trial and gives $x_1=-3/7$;
--   2. the second takes one trial and gives $x_2=1/14$;
--   3. the third takes two trials and gives $x_3=-3/56$;
--   4. for every $j\ge1$,
--   $$x_{2j}=\frac{4}{7\cdot 8^j},\qquad x_{2j+1}=-\frac{3}{7\cdot 8^j},$$
--   the line search from $x_{2j}$ to $x_{2j+1}$ takes two trials, and the line search from $x_{2j+1}$ to $x_{2j+2}$ takes one trial.
--
--   The example illustrates Theorem 5.2 with $a=(0,1,3,4,6,7,\dots)$, $a_{2r}=3r$, $a_{2r+1}=3r+1$.
--
--   **Formalization Note** The page says the line search from $x_{2j}$ to $x_{2j+1}$ ($j\ge1$) "takes just one trial, but from $x_{2j+1}$ to $x_{2j+2}$ takes two trials". This contradicts the page's own preceding sentence (from $x_2$ to $x_3$ takes two trials) and Theorem 5.2 ($N_k=a_k-a_{k-1}$ gives $N_{2j}=2$, $N_{2j+1}=1$); an exact rational simulation gives the trial counts $1,1,2,1,2,1,2,1,\dots$. The statement uses the corrected counts. Trial counts are numbered by the line search: $N_k$ is the number of trials producing $x_{k+1}$.
-- source:
--   Lewis, Overton, Nonsmooth optimization via quasi-Newton methods, Math. Program. Ser. A 141 (2013) 135–163, p. 153, §5.1, the example after Theorem 5.2 (trial counts of the repeating pattern corrected)

import Mathlib
import Definitions.Def_NonsmoothQN_Secant_Basic
import Definitions.Def_NonsmoothQN_Secant_Expansion

namespace NonsmoothQN.Secant

theorem example_four_sevenths :
    HasSum (fun r : ℕ => (2 : ℝ) ^ (-(3 * (r : ℤ))) - (2 : ℝ) ^ (-(3 * (r : ℤ)) - 1)) (4 / 7) ∧
    (∀ k : ℕ, secLSTerminates (4 / 7) 1 k) ∧
    secTrials (4 / 7) 1 0 = 1 ∧ secX (4 / 7) 1 1 = -3 / 7 ∧
    secTrials (4 / 7) 1 1 = 1 ∧ secX (4 / 7) 1 2 = 1 / 14 ∧
    secTrials (4 / 7) 1 2 = 2 ∧ secX (4 / 7) 1 3 = -3 / 56 ∧
    ∀ j : ℕ, 1 ≤ j →
      secX (4 / 7) 1 (2 * j) = 4 / (7 * 8 ^ j) ∧
      secX (4 / 7) 1 (2 * j + 1) = -3 / (7 * 8 ^ j) ∧
      secTrials (4 / 7) 1 (2 * j) = 2 ∧
      secTrials (4 / 7) 1 (2 * j + 1) = 1 := by sorry

end NonsmoothQN.Secant
