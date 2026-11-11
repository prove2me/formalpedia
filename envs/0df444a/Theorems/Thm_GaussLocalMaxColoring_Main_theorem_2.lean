-- Prove2me | Theorems.Thm_GaussLocalMaxColoring_Main_theorem_2
-- name    : GaussLocalMaxColoring.Main.theorem_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:22:46.495759+00:00
-- url     : https://prove2.me/theorems/578729f5-e23c-4c5f-88c6-381cc75addcc
-- title:
--   Theorem 2 — an ordinary vector $k$-coloring with $\Delta\le n^\beta$ yields, w.p. $\ge1-n^{-C}$, an independent set of size $n^{1-\frac{k-2}k\beta-o(1)}$ or $n^{1-\frac{(k-2)\beta}{2+k\beta}-o(1)}$
-- statement:
--   Fix a real $k>2$, $\beta\in(0,1]$ and $C>0$. There are constants $C_\ell$, $c_T>0$ and one function $g(n)\to0$ such that the algorithm of Theorem 2 (Appendix A: Algorithm 2 with the parameters of Lemmas 50/57, $\lceil c_T\log n\rceil$ independent trials, a largest independent set obtained) makes at most $Kn^K+K$ calls of Algorithm 1 for a constant $K$, and, on every graph $G$ on $n$ vertices with maximum degree at most $n^\beta$ given with an ordinary vector $k$-coloring (unit vectors with $\langle v_x,v_y\rangle\le-1/(k-1)$ on edges, any dimension), returns with probability at least $1-n^{-C}$ an independent set $I$ with
--   $$|I|\ge\begin{cases}n^{1-\frac{k-2}{k}\beta-g(n)},&0<\beta\le\frac{k-2}k,\\ n^{1-\frac{(k-2)\beta}{2+k\beta}-g(n)},&\frac{k-2}k<\beta\le1.\end{cases}$$
--
--   Differences from the source:
--   - reading: "there is a randomized polynomial-time algorithm" whose input contains real vectors → the paper's own algorithm (Algorithm 2 with the Lemma 50 / Lemma 57 parameters, ⌈c_T log n⌉ trials) for some constants C_ℓ, c_T, with at most K·n^K + K calls of Algorithm 1 (each O(n(n + d)) arithmetic operations on the vectors) and its success probability under the product Gaussian law of its samples; reason: analysis layer: real input vectors cannot be given to a bit-model machine without restricting them to rationals (a special case); a specific algorithm witnesses "there is an algorithm" (finding I1 records the missing bit-model analysis)
--   - reading: "Return the largest independent set obtained" (proof of Theorem 2) → a largest set among the SUCCESS sets and the sets sampled by failed trials; reason: a failed trial also obtains independent sets; when a trial succeeds the output is a largest successful set
--   - reading: o(1) in the exponent → one function g → 0 chosen after k, β, C and before the graph and vectors; reason: the paper's uniform asymptotic convention
--   - encoding: vertex set V with a fixed total order breaking ties → V = Fin n with its order; reason: Lean convention; every finite ordered vertex set is relabelled this way
--   - encoding: vectors in R^d, g ∼ N(0, I_d), P_g → Space d = EuclideanSpace ℝ (Fin d), any d, Mathlib stdGaussian (gaussProb); reason: Lean convention; same instances
-- source:
--   Deguchi, Kawarabayashi, Yoneda, Yoneda (2026), An O(n^0.1537)-Coloring Algorithm for 3-Colorable Graphs, arXiv:2610.35859 (SHA-256 9917b0a1…), Theorem 2, printed p. 4 (PDF 6); proof in Appendix A, p. 66 (PDF 68)

import Mathlib
import Definitions.Def_GaussLocalMaxColoring_Main_VectorRounding

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main
open Classical

namespace GaussLocalMaxColoring.Main

/-- **Theorem 2** (p. 4, PDF 6; proved in Appendix A, p. 66, PDF 68). Fix a real `k > 2`,
`β ∈ (0, 1]` and `C > 0`. The algorithm of Theorem 2 (Algorithm 2 with the parameters of
Lemmas 50 / 57, `⌈c_T log n⌉` independent trials, a largest independent set obtained), for suitable
constants `C_ℓ` and `c_T > 0`, makes polynomially many calls of Algorithm 1 and, on every graph
`G` on `n` vertices with maximum degree at most `n^β` given with an ordinary vector `k`-coloring
(any dimension), returns with probability at least `1 − n^{−C}` an independent set `I` with
`|I| ≥ n^{1 − ((k−2)/k)β − g(n)}` if `0 < β ≤ (k−2)/k` and `|I| ≥ n^{1 − (k−2)β/(2+kβ) − g(n)}` if
`(k−2)/k < β ≤ 1`, for one function `g → 0` fixed before the input. -/
theorem theorem_2 (k β : ℝ) (hk : 2 < k) (hβ0 : 0 < β) (hβ1 : β ≤ 1) (C : ℝ) (hC : 0 < C) :
    ∃ (Cl cT : ℝ) (g : ℕ → ℝ), 0 < cT ∧ IsLittleO1 g ∧
      (∃ K : ℝ, ∀ n : ℕ, (thm2Calls k β Cl cT n : ℝ) ≤ K * (n : ℝ) ^ K + K) ∧
      ∀ (n d : ℕ) (G : SimpleGraph (Fin n)) (v : Fin n → Space d),
        OrdinaryVectorColoring G v k → (maxDegOn G Finset.univ : ℝ) ≤ (n : ℝ) ^ β →
        (thm2Law n d k β Cl cT).real
            {ω | IsIndep G (thm2Output G v k β Cl cT ω) ∧
              (n : ℝ) ^ (thm2Exponent k β - g n) ≤ ((thm2Output G v k β Cl cT ω).card : ℝ)}
          ≥ 1 - (n : ℝ) ^ (-C) := by sorry

end GaussLocalMaxColoring.Main
