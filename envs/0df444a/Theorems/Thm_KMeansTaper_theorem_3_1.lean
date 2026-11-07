-- Prove2me | Theorems.Thm_KMeansTaper_theorem_3_1
-- name    : KMeansTaper.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:06:26.531908+00:00
-- url     : https://prove2.me/theorems/a7ddeee8-d4a9-4078-8999-db1c49531e57
-- title:
--   Theorem 3.1 — reduction theorem
-- statement:
--   Let $\kappa,c$ be rationals with $6.66\le\kappa\le8.25$ and $0<c\le1$ such that $\mathrm{SFI}(\kappa,c)$ holds. For every fixed $\varepsilon>0$ there is a deterministic algorithm, a Turing machine (`Turing.TM2ComputableInPolyTime`, every tape alphabet finite) running in time polynomial in the input length on the published instance code, which given an instance (a finite rational metric on $J\cup F$ and $1\le k\le|F|$) returns a nonempty $S\subseteq F$ with $|S|\le k$ and
--
--   $$\sum_{j\in J}d(j,S)^2\le\Bigl(1+\frac{\kappa}{e}+\varepsilon\Bigr)\mathrm{OPT}_k.$$
--
--   This reduces the approximation ratio of metric k-means to the finite inequality SFI.
--
--   **Formalization Note** The shape is that of the published `OAI.MetricKMedian.main_finite_work`; the output is the indicator list of $S$.
--
--   Differences from the source:
--   - encoding: a deterministic algorithm running in time polynomial in the input encoding, returning S → a Turing.TM2ComputableInPolyTime machine with finite alphabets over encodeInstance, outputting the indicator list of a nonempty S (CorrectRatio); reason: Lean model of deterministic polynomial time; the empty set has infinite cost in the paper
--   - encoding: 6.66, 8.25 → the exact rationals 666/100, 825/100; reason: same numbers
-- source:
--   Zhu, A tight approximation for metric k-means via squared tapered rounding, STOC 2027 submission (manuscript sha256 8b6610229e43dc2441325b120437136afe762dbd6e873f73919fcb6b043fc5a3), Theorem 3.1, p.4 (PDF p.7); proof p.18 (PDF p.21)

import Mathlib
import Definitions.Def_MetricKMedian
import Definitions.Def_KMeansTaper_CorrectRatio
import Definitions.Def_KMeansTaper_SFI

namespace KMeansTaper

open OAI.MetricKMedian (Instance encodeInstance)

/-- **Theorem 3.1 (reduction theorem)**, p.4 (PDF p.7).

Zhu, *A tight approximation for metric k-means via squared tapered rounding*, STOC 2027
submission (manuscript sha256 8b6610229e43dc2441325b120437136afe762dbd6e873f73919fcb6b043fc5a3).

Let `κ, c` be rational with `6.66 ≤ κ ≤ 8.25` and `0 < c ≤ 1`, such that `SFI(κ, c)` holds.
For every fixed `ε > 0` there is a deterministic algorithm which, given a finite rational metric
`(J ∪ F, d)` and `1 ≤ k ≤ |F|`, returns `S ⊆ F` with `|S| ≤ k` and
`∑_{j ∈ J} d(j, S)² ≤ (1 + κ/e + ε) OPT_k`, in time polynomial in the input encoding.

**Formalization Note.** As in the published `OAI.MetricKMedian.main_finite_work`: a
`Turing.TM2ComputableInPolyTime` machine with finite alphabets over the published
`encodeInstance`, whose output is the indicator bit-list of `S` (`CorrectRatio`). -/
theorem theorem_3_1 (κ c : ℚ) (hκ1 : 666 / 100 ≤ κ) (hκ2 : κ ≤ 825 / 100) (hc0 : 0 < c)
    (hc1 : c ≤ 1) (hSFI : SFI κ c) (ε : ℝ) (hε : 0 < ε) :
    ∃ (algorithm : Instance → List Bool)
      (M : Turing.TM2ComputableInPolyTime encodeInstance id algorithm),
      (∀ k : M.tm.K, Finite (M.tm.Γ k)) ∧
      ∀ I, CorrectRatio (1 + κ / Real.exp 1 + ε) I (algorithm I) := by sorry

end KMeansTaper
