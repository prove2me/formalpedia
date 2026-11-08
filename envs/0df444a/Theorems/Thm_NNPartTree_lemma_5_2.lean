-- Prove2me | Theorems.Thm_NNPartTree_lemma_5_2
-- name    : NNPartTree.lemma_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:11:51.157484+00:00
-- url     : https://prove2.me/theorems/657421a3-dc8e-4e7e-90ce-e95e4fe32ad5
-- title:
--   Lemma 5.2, p.16 (corrected: $\mathcal F$ has a $\beta$-balanced member) — randomized finder of a low-energy, low-kurtosis polynomial
-- statement:
--   There are a program without `sample`, a constant $c$ and an exponent $K$ with the following. On input $d,k,\beta\in(0,1/2],\varepsilon\in(0,\beta/8)$ and a sample $S$ of $m\ge c/\beta^2$ pairs, it halts within $c((d+k)^km/\varepsilon)^K$ work on every $S$ and every coin tape. If $\mathcal F$ is a cut class with a $\beta$-balanced member and approximation degree at most $k$ at $\varepsilon$, then with probability at least $1/10$ over $S\sim\mathcal D^m$ and the coins, the output polynomial $A$, of degree at most $k$, has positive variance on $S_Y$ and
--   $$R_S(A)\le\frac c\beta\big(\mathrm{OPT}_\beta(\mathcal F)+\varepsilon\big)\quad\text{and}\quad\gamma(A;S_Y)\le\frac c{\beta^2}.$$
--
--   Differences from the source:
--   - reading: no machine is named → the sampling real RAM `NNPartTree.Machine`; reason: the paper leaves the model open
--   - correction: F any cut class → F has a member of balance at least β; reason: OPT_β(F) is a minimum over the empty set otherwise; for D a point mass no polynomial has positive variance on S_Y, so R and γ are 0/0
--   - generalization: OPT_β(F) a minimum → an infimum; reason: a minimum need not be attained on an infinite class; when it is, the two agree
--   - reading: inputs: samples, β, ε → k = k(ε) is also an input, as an upper bound on the degree at ε; reason: the printed list omits it, and the program cannot compute a degree of an unknown class (see Theorem 3)
--   - encoding: a degree-k(ε) polynomial, the bounds on R and γ → coefficient vector in the order of `monomials d k`; positive variance in the event; d ≥ 1; reason: degree at most k holds by construction, and x/0 = 0 would make the R bound free
--   - encoding: with probability at least 1/10 → failure set has outer measure at most 9/10; reason: no measurability is claimed
-- source:
--   Khanna, Padaki, Waingarten, Learning Partition Trees for Nearest Neighbor Search, arXiv:2607.09909 (held copy of 2026-11-03, sha256 d32992f2…), Lemma 5.2, p.16; proof p.20

import Mathlib
import Definitions.Def_NNPartTree_Learner

open MeasureTheory

namespace NNPartTree

/-- **Lemma 5.2** (Low-Energy and Kurtosis Polynomial Finder), p.16; proof p.20. S. Khanna, A. Padaki, E. Waingarten, *Learning Partition Trees for Nearest Neighbor Search*, arXiv:2607.09909 (held copy of 2026-11-03, sha256 d32992f2…).

There is a randomized program that receives `m ≥ c/β²` samples, `k`, `β ∈ (0, 1/2]` and `ε ∈ (0, β/8)`, halts on every
sample and coin tape within `c ((d + k)^k m/ε)^K` work, and, when `D` has `F`-approximation degree `k` at `ε`, outputs with
probability at least `1/10` a polynomial `A` of degree at most `k` with `R_S(A) ≤ (c/β)(OPT_β(F) + ε)` and
`γ(A; S_Y) ≤ c/β²`.

**Formalization Note.** `k = k(ε)` is an input (see Theorem 3). `F` has a `β`-balanced member, which is needed for
`OPT_β(F)` to be an infimum over a nonempty set, and `OPT_β` is an infimum. Positive variance on `S_Y` is part of the
event, because `x/0 = 0` would make the `R` bound free. The output is a coefficient vector in the order of
`monomials d k`, so its degree is at most `k` by construction. The failure set is bounded in outer measure. -/
theorem lemma_5_2 : ∃ Finder : Program, NoSample Finder ∧ ∃ c : ℝ, 0 < c ∧ ∃ K : ℕ,
    ∀ (d k m : ℕ) (β ε : ℝ), 1 ≤ d → 0 < β → β ≤ 1 / 2 → 0 < ε → ε < β / 8 → c / β ^ 2 ≤ m →
      (∀ (S : Fin m → Pt d × Pt d) (coins : ℕ → Bool), ∃ st,
        IsFinal Finder 0 (sampleInput k S β ε) (coins, noStream) st ∧
        (st.work : ℝ) ≤ c * (((d : ℝ) + k) ^ k * m * (1 / ε)) ^ K) ∧
      ∀ (D : Measure (Pt d × Pt d)) [IsProbabilityMeasure D] (F : Set (Pt d → ℝ)),
        (∀ f ∈ F, IsCut f) → (∃ f ∈ F, β ≤ bal D f) → (∀ f ∈ F, ApproxAt D f ε k) →
        ((sampleProduct D m).prod coinTape) {ω | ¬ ∃ st,
            IsFinal Finder 0 (sampleInput k ω.1 β ε) (ω.2, noStream) st ∧
            0 < varOn (marginalY (empirical ω.1)) (outputPoly k st) ∧
            energy (empirical ω.1) (outputPoly k st) ≤ c / β * (opt D β F + ε) ∧
            kurtosis (marginalY (empirical ω.1)) (outputPoly k st) ≤ c / β ^ 2} ≤
          ENNReal.ofReal (9 / 10) := by sorry

end NNPartTree
