-- Prove2me | Theorems.Thm_MetricTSPSublinear_lemma_9_1_timed
-- name    : MetricTSPSublinear.lemma_9_1_timed
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-27T00:05:08.347784+00:00
-- url     : https://prove2.me/theorems/e91130c0-0e85-4ec3-9468-0f0a08021073
-- title:
--   Lemma 9.1, timed and amplified: the estimator $\widehat L$ w.p. $5/6$
-- statement:
--   Let $d$ be a metric on $n$ points, accessed only through distance queries. Let $M$ be the MST weight, $K$ the value of the cut LP on all points, and $D=M-K$.
--
--   There are constants $\varepsilon\in(0,1]$, $\gamma,\eta>0$ and $C$ and an admissible program $P$ of the distance-oracle real RAM with fair coins (`SublinearSteiner`) such that, for every $n$ and every metric $d$ on $n$ points, with $B=\lceil C(n+1)^{2-\gamma}\rceil$:
--
--   1. for every real $\widehat M$ placed in real memory cell $0$ and every tape of $B$ coins, $P$ halts within $B$ steps after at most $C(n+1)^{2-\eta}$ distance queries;
--   2. for every $\widehat M$ with $M\le\widehat M\le(1+\varepsilon/4)M$, on at least a $5/6$ fraction of the tapes the output $\widehat L$ satisfies
--   $$0\le \widehat L\le K\qquad\text{and}\qquad D\le\varepsilon M\ \Longrightarrow\ \widehat L\ge\frac{1+\varepsilon}{2}\,\widehat M .$$
--
--   This is Lemma 9.1 of Azarmehr–Behnezhad together with the running-time claim of their Theorem 1 ("the algorithm runs in $O(n^{2-\gamma})$ time"), at one fixed admissible choice of $\varepsilon$ and $a$. Combined with an MST estimator and the decision rule of §9, it yields Theorem 1.
--
--   **Formalization Note.**
--   * Lemma 9.1 is stated with success probability $2/3$ and no time bound. Here the time bound comes from the implementation discussion in §9.4 (p.42–43, PDF p.44–45). Success probability $5/6$ comes from taking the median of a constant number of independent runs; the median preserves both clauses, since each clause is a one-sided bound.
--   * The halting and query bounds are required for every real $\widehat M$, not only for accurate ones. The algorithm enforces its budget: "a subroutine that exceeds its budget stops and returns zero" (p.42). Without this, a composite algorithm could fail to halt when the MST estimate is bad.
--   * The constant of the page's $O(\varepsilon)$ in the accuracy of $\widehat M$ is fixed to $1/4$. The machine, start state (`runWithEstimate`) and tape convention are those of the milestone statement of Lemma 9.1.
-- source:
--   A. Azarmehr, S. Behnezhad, Metric TSP in Sublinear Time: Breaking Two Approximation, arXiv:2611.04283 (held version, sha256 a86ea2397da2e82c8f8baada200e333f32a133395de02943b1fce22946e4a745), https://arxiv.org/abs/2611.04283, §9, Lemma 9.1, p.33 (PDF p.35); running time: Theorem 1, p.1 (PDF p.3) and §9.4, p.42-43 (PDF p.44-45)

import Mathlib
import Definitions.Def_SublinearSteiner_Machine
import Definitions.Def_DoublingMST_IsMetric
import Definitions.Def_DoublingMST_mstWeight
import Definitions.Def_MetricTSPSublinear_cutLP
import Definitions.Def_MetricTSPSublinear_runWithEstimate

open scoped Classical

namespace MetricTSPSublinear

theorem lemma_9_1_timed :
    ∃ (ε γ η : ℝ) (P : SublinearSteiner.Program) (C : ℝ), 0 < ε ∧ ε ≤ 1 ∧ 0 < γ ∧ 0 < η ∧
      SublinearSteiner.Admissible P ∧
      ∀ (n : ℕ) (d : Fin n → Fin n → ℝ), DoublingMST.IsMetric d →
        (∀ (Mhat : ℝ) (tape : Fin ⌈C * ((n : ℝ) + 1) ^ (2 - γ)⌉₊ → Bool),
            (runWithEstimate P d Mhat tape ⌈C * ((n : ℝ) + 1) ^ (2 - γ)⌉₊).output.isSome ∧
            ((runWithEstimate P d Mhat tape ⌈C * ((n : ℝ) + 1) ^ (2 - γ)⌉₊).queries : ℝ) ≤
              C * ((n : ℝ) + 1) ^ (2 - η)) ∧
        ∀ Mhat : ℝ, DoublingMST.mstWeight d ≤ Mhat → Mhat ≤ (1 + ε / 4) * DoublingMST.mstWeight d →
          (5 / 6 : ℝ) * 2 ^ ⌈C * ((n : ℝ) + 1) ^ (2 - γ)⌉₊ ≤
            ((Finset.univ.filter (fun tape : Fin ⌈C * ((n : ℝ) + 1) ^ (2 - γ)⌉₊ → Bool => ∃ L : ℝ,
                (runWithEstimate P d Mhat tape ⌈C * ((n : ℝ) + 1) ^ (2 - γ)⌉₊).output = some L ∧
                0 ≤ L ∧ L ≤ cutLP d Finset.univ ∧
                (DoublingMST.mstWeight d - cutLP d Finset.univ ≤ ε * DoublingMST.mstWeight d →
                  (1 + ε) / 2 * Mhat ≤ L))).card : ℝ) := by sorry

end MetricTSPSublinear
