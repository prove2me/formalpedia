-- Prove2me | Theorems.Thm_LDPSelect_Supplement_theorem_18
-- name    : LDPSelect.Supplement.theorem_18
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:07:47.271888+00:00
-- url     : https://prove2.me/theorems/5a915114-2b6d-45ad-9a56-40b83c9d74a7
-- title:
--   Theorem 18 — finite-$n$ multi-selection bound $W^{\mathrm N}_k\ge \frac{ak(1-\eta)}{(a+1)m}M_k$
-- statement:
--   Let $1\le k\le n$ and $a\ge1$. Put
--   $$L=\frac{n+(a-1)k}{a+1},$$
--   take $s>\sqrt L$, and let $m=\max\{k,\lceil L+s\rceil\}$ and $\eta=L/s^2$. Then every product prior satisfies
--   $$W^{\mathrm N}_k\ \ge\ \frac{ak(1-\eta)}{(a+1)m}\,M_k,$$
--   where $W^{\mathrm N}_k$ is the optimal non-interactive reward for selecting at most $k$ users and $M_k=\mathbb E[\text{sum of the }k\text{ largest values}]$.
--
--   This is the explicit finite-$n$ bound from which the lower half of Theorem 6 follows.
--
--   **Formalization Note** The coefficient is read through the map $\mathbb R\to[0,\infty]$ that sends negative numbers to $0$; when $\eta>1$ the coefficient is negative and the inequality is trivial both in the paper and in Lean.
--
--   Differences from the source:
--   - encoding: the coefficient ak(1 − η)/((a + 1)m) → ENNReal.ofReal of the real expression; reason: values in [0, ∞]; a negative coefficient (η > 1) becomes 0, and the inequality is trivial in both readings
--   - encoding: ⌈L + s⌉ → Nat.ceil (L + s); reason: L + s > 0
--   - encoding: every product prior → every family of probability measures on ℝ≥0 with finite means, indexed by arrival position; reason: the standing assumption of §2: values are independent, non-negative and integrable
--   - encoding: W^I and W^N of Definition 8 → the published WI and WN (suprema in [0, ∞] over output types Z : Type and private mechanisms with behaviour-strategy acceptance kernels); reason: the published base model of this mission, whose conventions are listed with LDPSelect.theorem_1
-- source:
--   Chen, Wang, When Does Private Data Collection Need Interaction? Online Selection under Local Differential Privacy, STOC 2027 submission (manuscript sha256 2e2d6157…), Theorem 18, p.12 (pdf p.13)

import Mathlib
import Definitions.Def_LDPSelect_Values
import Definitions.Def_LDPSelect_Supplement_Matroid

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LDPSelect.Supplement

open LDPSelect

/-- Chen, Wang, *When Does Private Data Collection Need Interaction? Online Selection under Local Differential Privacy*, STOC 2027 submission (manuscript sha256 2e2d6157…), Theorem 18, p.12 (pdf p.13).

Let `1 ≤ k ≤ n` and `a ≥ 1`. Put `L = (n + (a−1)k)/(a+1)`, take `s > √L`, and let `m = max{k, ⌈L + s⌉}`
and `η = L/s²`. Then every product prior satisfies `W^N_k ≥ ak(1 − η)/((a + 1)m) M_k`.

**Formalization Note.** `W^N_k` and `M_k` are `WN` and `prophet` on `U_{k,n} = unifFam k n`. A product prior
is a family of probability measures with finite means. `⌈L + s⌉` is `Nat.ceil` of a positive real. The
coefficient is read through `ENNReal.ofReal`; when `η > 1` it is negative, `ofReal` makes it `0`, and the
paper's inequality is trivial in that case as well. -/
theorem theorem_18 (n k : ℕ) (hk1 : 1 ≤ k) (hkn : k ≤ n) (a : ℝ) (ha : 1 ≤ a) (s : ℝ)
    (hs : Real.sqrt ((n + (a - 1) * k) / (a + 1)) < s)
    (P : Fin n → Measure ℝ≥0) (hP : ∀ i, IsProbabilityMeasure (P i)) (hint : IsIntegrablePrior P) :
    let L : ℝ := (n + (a - 1) * k) / (a + 1)
    let m : ℕ := max k ⌈L + s⌉₊
    let η : ℝ := L / s ^ 2
    ENNReal.ofReal (a * k * (1 - η) / ((a + 1) * m)) * prophet (unifFam k n) P ≤
      WN a (unifFam k n) P := by sorry

end LDPSelect.Supplement
