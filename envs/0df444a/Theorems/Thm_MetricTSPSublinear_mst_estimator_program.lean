-- Prove2me | Theorems.Thm_MetricTSPSublinear_mst_estimator_program
-- name    : MetricTSPSublinear.mst_estimator_program
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-27T00:05:04.273819+00:00
-- url     : https://prove2.me/theorems/eec2dc44-7a3c-5a11-a134-0f28d4eedc60
-- title:
--   Sublinear MST-weight estimator: $M\le\widehat M\le(1+\eta)M$ w.p. $5/6$
-- statement:
--   Let $d$ be a metric on $n$ points, accessed only through distance queries, and let $M$ be the weight of a minimum spanning tree of $d$.
--
--   For every accuracy $\eta>0$ there are constants $\varepsilon,\gamma>0$ and $C$ and an admissible program $P$ of the distance-oracle real RAM with fair coins (the `SublinearSteiner` machine) with the following property. For every $n$ and every metric $d$ on $n$ points, put $B=\lceil C(n+1)^{2-\gamma}\rceil$. Then:
--
--   1. on every tape of $B$ coins, $P$ halts within $B$ steps after at most $C(n+1)^{2-\varepsilon}$ distance queries;
--   2. on at least a $5/6$ fraction of the $2^B$ tapes the output $\widehat M$ satisfies
--   $$M\le \widehat M\le (1+\eta)\,M .$$
--
--   This is the MST-weight estimate $\widehat M$ that Azarmehr and Behnezhad assume throughout their paper (§3, p.9: "we assume access to an estimation $\widehat M$ satisfying $M\le\widehat M\le(1+O(\varepsilon))M$, which is obtainable using $\widetilde O(n/\varepsilon^{O(1)})$ queries [9]"). Together with a timed version of their Lemma 9.1, it is one of the two subroutines in the proof of their Theorem 1.
--
--   **Formalization Note.** The source result (Czumaj–Sohler) gives a $(1\pm\eta')$-approximation with constant success probability in $\widetilde O(n\,\eta'^{-O(1)})$ time and queries. The one-sided form $M\le\widehat M\le(1+\eta)M$ comes from dividing by $1-\eta'$. Success probability $5/6$ comes from taking the median of a constant number of independent runs. The bounds stated here, $n^{2-\gamma}$ steps and $n^{2-\varepsilon}$ queries, are weaker than $\widetilde O(n)$. The machine is the published `SublinearSteiner` real RAM: no floor, logarithm or square root, and fair coins are the only randomness. The input is $n$ in integer memory cell $0$, with terminal set `Finset.univ`. Both bounds hold on every tape.
-- source:
--   A. Czumaj, C. Sohler, Estimating the weight of metric minimum spanning trees in sublinear-time, STOC 2004, pp. 175-183 (doi:10.1145/1007352.1007386), main theorem; used as the estimate M-hat in A. Azarmehr, S. Behnezhad, Metric TSP in Sublinear Time: Breaking Two Approximation, arXiv:2611.04283 (held version, sha256 a86ea239...), §3, p.9 (PDF p.11-12), reference [9]

import Mathlib
import Definitions.Def_SublinearSteiner_Machine
import Definitions.Def_DoublingMST_IsMetric
import Definitions.Def_DoublingMST_mstWeight

open scoped Classical

namespace MetricTSPSublinear

theorem mst_estimator_program :
    ∀ η : ℝ, 0 < η → ∃ (ε γ : ℝ) (P : SublinearSteiner.Program) (C : ℝ), 0 < ε ∧ 0 < γ ∧
      SublinearSteiner.Admissible P ∧
      ∀ (n : ℕ) (d : Fin n → Fin n → ℝ), DoublingMST.IsMetric d →
        (∀ tape : Fin ⌈C * ((n : ℝ) + 1) ^ (2 - γ)⌉₊ → Bool,
            (SublinearSteiner.run P Finset.univ d tape ⌈C * ((n : ℝ) + 1) ^ (2 - γ)⌉₊).output.isSome ∧
            ((SublinearSteiner.run P Finset.univ d tape ⌈C * ((n : ℝ) + 1) ^ (2 - γ)⌉₊).queries : ℝ) ≤
              C * ((n : ℝ) + 1) ^ (2 - ε)) ∧
        (5 / 6 : ℝ) * 2 ^ ⌈C * ((n : ℝ) + 1) ^ (2 - γ)⌉₊ ≤
          ((Finset.univ.filter (fun tape : Fin ⌈C * ((n : ℝ) + 1) ^ (2 - γ)⌉₊ → Bool => ∃ z : ℝ,
              (SublinearSteiner.run P Finset.univ d tape ⌈C * ((n : ℝ) + 1) ^ (2 - γ)⌉₊).output = some z ∧
              DoublingMST.mstWeight d ≤ z ∧ z ≤ (1 + η) * DoublingMST.mstWeight d)).card : ℝ) := by sorry

end MetricTSPSublinear
