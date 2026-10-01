-- Prove2me | Theorems.Thm_MurtyKabadi_Reduction_subsetSum_tfae
-- name    : MurtyKabadi.Reduction.subsetSum_tfae
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:19:01.460382+00:00
-- url     : https://prove2.me/theorems/3e53a115-453b-4f03-ab0b-8dada15b3c0a
-- title:
--   Theorems 1–3 and §4 (reduction): subset sum is solvable iff $0$ is not a local min of $x^{\mathsf T}Mx$ on $x\ge0$, iff $M$ is not copositive, iff …
-- statement:
--   Let $d_0; d_1, \dots, d_n$ be positive integers, the data of a subset sum instance, and let $l$ be the total number of decimal digits in these data. Let $\delta$ be an integer and $\varepsilon$ a rational number with
--   $$\delta > 4\Big(d_0 \sum_{j=1}^n d_j\Big)^2 n^3, \qquad 0 < \varepsilon < 2^{-n l^2}.$$
--   Let $M$ be the symmetric $2n \times 2n$ matrix of the quadratic form $f_5$ in the variables $(y, s)$, and $Q(x) = x^{\mathsf T}Mx$. The following are equivalent:
--
--   1. the subset sum instance is solvable (some subset of $\{d_1, \dots, d_n\}$ sums to $d_0$);
--   2. $x = 0$ is not a local minimum of $Q$ on $\{x \ge 0\}$ (Problem 1);
--   3. $Q$ is not bounded below on $\{x \ge 0\}$ (Problem 2);
--   4. there is $x \ge 0$ with $Q(x) < 0$ (Problem 3);
--   5. $M$ is not copositive;
--   6. there is $x \ge 0$ with $e^{\mathsf T}x = n$ and $Q(x) < 0$ (Problem 4 with $a_0 = n$);
--   7. $u = 0$ is not a local minimum of $h(u) = (u^2)^{\mathsf T} M (u^2)$ on $\mathbb R^{2n}$ (Problem 11);
--   8. $h$ is not bounded below on $\mathbb R^{2n}$ (Problem 12).
--
--   This is the mathematical content of the paper's Theorems 1–3 and §4: the explicit map from $(d_0; d_1, \dots, d_n)$ to $M$ is a reduction from subset sum to each of these questions, so each of them is NP-hard; in particular deciding whether a feasible point of a quadratic program is a local minimum, and deciding copositivity, are NP-hard.
--
--   **Formalization Note** Only the correctness of the reduction is formalized. Not formalized: membership in NP (Lemma 1), the polynomial-time computability of $M$ from the data, the encoding size of $M$, and the NP-completeness of subset sum (cited in the paper from Garey–Johnson). $M$ has rational entries ($\varepsilon$ is rational and $(d_0^2 - n\delta)/n^2$ need not be an integer); a positive integer multiple of it is the integer matrix of Theorem 3, has the same answer to every question in the list, and this rescaling is not formalized. The paper's §3 standing assumption "$D$ is not PSD" is not imposed ($M$ can be PSD, e.g. $n = 1$, $d_1 = 5$, $d_0 = 1$), and the equivalence holds without it. The bound on $\varepsilon$ is written $\varepsilon \cdot 2^{nl^2} < 1$ in $\mathbb Q$; $l$ counts decimal digits. For $n = 0$ all eight statements are false, so no hypothesis $n \ge 1$ is needed.
-- source:
--   Murty and Kabadi, Some NP-complete problems in quadratic and nonlinear programming, Math. Programming 39 (1987), pp. 124–125, Theorems 1, 2, 3 and their proofs; pp. 126–127, §4 (Problems 11 and 12)

import Mathlib
import Definitions.Def_MurtyKabadi_Reduction_QuadraticProblems
import Definitions.Def_MurtyKabadi_Reduction_SubsetSum
import Definitions.Def_MurtyKabadi_Reduction_Construction

namespace MurtyKabadi.Reduction

theorem subsetSum_tfae {n : ℕ} (d : Fin n → ℕ) (d0 δ : ℕ) (ε : ℚ)
    (hd : ∀ j, 0 < d j) (hd0 : 0 < d0)
    (hδ : 4 * (d0 * ∑ j, d j) ^ 2 * n ^ 3 < δ)
    (hε0 : 0 < ε) (hε : ε * (2 : ℚ) ^ (n * digitCount d d0 ^ 2) < 1) :
    List.TFAE
      [SubsetSumSolvable d d0,
       Problem1 (mkMatrix d d0 δ ε),
       Problem2 (mkMatrix d d0 δ ε),
       Problem3 (mkMatrix d d0 δ ε),
       ¬ Copositive (mkMatrix d d0 δ ε),
       Problem4 (mkMatrix d d0 δ ε) n,
       Problem11 (mkMatrix d d0 δ ε),
       Problem12 (mkMatrix d d0 δ ε)] := by sorry

end MurtyKabadi.Reduction
