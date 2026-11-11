-- Prove2me | Theorems.Thm_IterRoundKMedian_Main_lemma_7_11
-- name    : IterRoundKMedian.Main.lemma_7_11
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:28:56.695551+00:00
-- url     : https://prove2.me/theorems/f196c16f-b8d5-4377-86c5-de0a02727f25
-- title:
--   Lemma 7.11 — robust rounding: E[d(j, F_open)] ≤ (1 − 1/e)V_j + (3/e)A_j
-- statement:
--   Let $S$ be a complete fractional solution with $y(F)\ge1$. Choose a threshold radius $R_j$ for every client, run the filtering procedure (representatives $\mathcal R$, ties arbitrary), form the bundles $U_r$, run the greedy matching $\mathcal M$ of $\mathcal R$ (ties arbitrary), and let $Y$ follow a law with the dependent-rounding properties (85)–(89) for this laminar family; $F_{\rm open}=\{i\in F: Y_i=1\}$. Then for every client $j\in C$,
--   $$\mathbb E\big[d(j,F_{\rm open})\big]\ \le\ \Big(1-\frac1e\Big)V_j+\frac3e\,A_j.$$
--
--   Together with Lemma 7.3 and Lemma 7.5 this gives the guarantee of the robust algorithm (Theorem 7.1), the second rounding combined in §8.
--
--   Differences from the source:
--
--   - generalization: F_open from the dependent rounding of [Sri01] on the laminar family {F} ∪ {U_r ∪ U_s} ∪ {U_r} → any law of Y satisfying (85)–(89) (IsRobustRounding); reason: the proof uses only (85)–(89), which the paper states for [Sri01]'s rounding, so the statement specializes to the source
--   - generalization: a complete nearest-unit support for every client → a complete solution (x_ij ∈ {0, y_i}, Σ_i x_ij = 1) without the nearest-unit ordering; reason: the proofs of Observation 7.6 to Lemma 7.11 do not use the ordering; nearest-unit solutions are complete solutions
--   - reading: R_j the minimizing radius, the client with minimum A_r, the two closest representatives (tie-breaking unspecified) → any minimizer R_j (IsThreshold), any run of the filtering and of the greedy matching (FilterRun, GreedyMatching); reason: the page fixes no tie-breaking; the Lean statement covers every choice
--   - encoding: facilities split into colocated copies → a pseudometric d on a finite point set; reason: copies are distinct points at distance 0
--   - encoding: d(j, F_open) → distOpen, defined as 0 when F_open = ∅; reason: F_open = ∅ has probability 0 by (85) since y(F) ≥ 1
-- source:
--   Byrka, Guo, Hu, Li, Shin, Vajanopath, Wan, Wang, Iterative Randomized Rounding for k-Median in General and Euclidean Metrics, STOC 2027 submission (manuscript sha256 02f6267b…), p. 69, Lemma 7.11 (algorithm on pp. 66–68)

import Mathlib
import Definitions.Def_IterRoundKMedian_Main_PipageLaw
import Definitions.Def_IterRoundKMedian_Main_Robust

namespace IterRoundKMedian.Main

open Robust in
theorem lemma_7_11 {P : Type*} [Fintype P] [DecidableEq P] (S : Solution P) (Rad : P → ℝ)
    (hRad : ∀ j ∈ S.C, IsThreshold S j (Rad j))
    (reps : List P) (hfilter : FilterRun S Rad S.C reps)
    (M : List (P × P)) (hmatch : GreedyMatching S reps.toFinset M)
    (μ : FinLaw (P → Bool)) (hμ : IsRobustRounding S reps M μ) :
    ∀ j ∈ S.C, μ.expect (fun Y => distOpen S Y j) ≤
      (1 - 1 / Real.exp 1) * Vj S j + 3 / Real.exp 1 * assurance S Rad j := by sorry

end IterRoundKMedian.Main
