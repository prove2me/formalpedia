-- Prove2me | Theorems.Thm_LefebvreVariations_lonely_runner_small_coprime_no_top_gap
-- name    : LefebvreVariations.lonely_runner_small_coprime_no_top_gap
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-24T21:41:01.335594+00:00
-- url     : https://prove2.me/theorems/78619544-1f02-44ad-906e-fe9f7c281ec7
-- title:
--   Lefebvre's variations, No. 2 — on a theme by Wills: the lonely runner with four to seven runners, coprime speeds and no gap at the top
-- statement:
--   For a real number $x$ write $\|x\| = \min_{z \in \mathbb{Z}} |x - z|$ for its distance to the nearest integer.
--
--   Let $3 \le k \le 6$ and let $S = \{v_1 < v_2 < \dots < v_k\}$ be a set of $k$ positive integers such that
--
--   1. $\gcd(v_1, \dots, v_k) = 1$, and
--   2. the largest speed is less than $k$ times the second largest: $v_k < k\, v_{k-1}$.
--
--   Then there is a real number $t$ with
--
--   $$
--   \| t\, v \| \ge \frac{1}{k+1} \qquad \text{for every } v \in S .
--   $$
--
--   In the language of the lonely runner conjecture: $k$ runners with distinct positive integer speeds $v \in S$ and one runner standing still at $0$, on a circular track of length $1$; at time $t$ every moving runner is at distance at least $\frac{1}{k+1}$ from the still one. The statement is the special case, for $k$ moving runners with $3 \le k \le 6$ (four to seven runners in all), of the theorems of Betke–Wills and Cusick ($k=3$), Cusick–Pomerance ($k=4$), Bohman–Holzman–Kleitman ($k=5$) and Barajas–Serra ($k=6$), restricted to coprime speed sets without a gap at the top. The bound is sharp inside this class: $S = \{1, 2, \dots, k\}$ satisfies both conditions and admits no time with $\|tv\| > \frac{1}{k+1}$ for all $v$.
--
--   **Formalization Note** The distance to the nearest integer is `LonelyRunnerConjecture.distToNearestInt x = min (fract x) (1 - fract x)`, which equals $\|x\|$. The speeds form a `Finset ℕ` of cardinality `k` with positive elements, as in `LonelyRunnerConjecture.LRC k`. The gcd condition is `S.gcd id = 1`. The condition $v_k < k\,v_{k-1}$ is written without sorting: there are $a, b \in S$ with $a < b$, $b$ the maximum of $S$, and $b < k a$ (this holds for some $a$ exactly when it holds for the second largest element).
-- source:
--   Special case of the lonely runner theorems for k ≤ 6 moving runners: U. Betke and J. M. Wills, Untere Schranken für zwei diophantische Approximations-Funktionen, Monatsh. Math. 76 (1972), 214–217, and T. W. Cusick, View-obstruction problems in n-dimensional Euclidean space and a generalization of them, Aequationes Math. 9 (1973) (k = 3); T. W. Cusick and C. Pomerance, View-obstruction problems III, J. Number Theory 19 (1984), 131–139 (k = 4); T. Bohman, R. Holzman and D. Kleitman, Six lonely runners, Electron. J. Combin. 8(2) (2001), R3, and J. Renault, View-obstruction: a shorter proof for 6 lonely runners, Discrete Math. 287 (2004) (k = 5); J. Barajas and O. Serra, The lonely runner with seven runners, Electron. J. Combin. 15 (2008), R48 (k = 6). Conjecture: J. M. Wills (1967), T. W. Cusick (1973). Origin of this statement: it is the missing step of a reduction of LonelyRunnerConjecture.classical_small_cases (LRC k for all k ≤ 6). The verified reduction proves LRC 0 directly, proves LRC 2 for coprime pairs (Wills, via the times j/(a+b)), proves a top-gap lemma (if LRC(k−1) holds and the largest speed is at least k times every other speed, a lonely time exists, by perturbing a lonely time of the k−1 smaller speeds), and divides any speed set by its gcd; the case left is exactly this statement.

import Definitions.Def_LonelyRunnerConjecture_Defs

set_option autoImplicit false

namespace LefebvreVariations
theorem lonely_runner_small_coprime_no_top_gap (k : ℕ) (hk3 : 3 ≤ k) (hk6 : k ≤ 6)
    (S : Finset ℕ) (hS : S.card = k) (hpos : ∀ v ∈ S, 0 < v)
    (hgcd : S.gcd id = 1)
    (hgap : ∃ a ∈ S, ∃ b ∈ S, a < b ∧ (∀ v ∈ S, v ≤ b) ∧ b < k * a) :
    ∃ t : ℝ, ∀ v ∈ S, (1 : ℝ) / (k + 1 : ℝ) ≤
      LonelyRunnerConjecture.distToNearestInt (t * (v : ℝ)) := by sorry
end LefebvreVariations
