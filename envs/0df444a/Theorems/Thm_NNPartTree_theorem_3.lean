-- Prove2me | Theorems.Thm_NNPartTree_theorem_3
-- name    : NNPartTree.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:12:48.149687+00:00
-- url     : https://prove2.me/theorems/3a5c4b20-92d6-49b6-8640-e10cccde7a78
-- title:
--   Theorem 3, pp.14–15 (corrected: $\mathcal F$ has a $\beta$-balanced member, $k_0$ an input, $\log(2/\delta)$) — PolyCut
-- statement:
--   There are a randomized program PolyCut with sample access, a constant $c$ and an exponent $K$ with the following. On input $d\ge1$, $\beta\in(0,1/2]$, $\varepsilon,\delta\in(0,1)$ and $k_0$, on every run it uses at most $c(d+k_0)^{k_0}(1/\varepsilon^2+1/\beta^4)\log(2/\delta)$ samples and at most $c((d+k_0)^{k_0}(1/(\beta\varepsilon))\log(2/\delta))^K$ work. If $\mathcal F$ is a cut class with a member of balance at least $\beta$ and approximation degree at most $k_0$ at $\varepsilon_0=\min\{\varepsilon,\beta/9\}$, then with probability at least $1-\delta$ the output degree-$k_0$ polynomial threshold function $g$ satisfies
--   $$\mathrm{err}_{\mathcal D}(g)\le c\sqrt{\big(\mathrm{OPT}_\beta(\mathcal F)+\varepsilon\big)/\beta}\quad\text{and}\quad\mathrm{bal}_{\mathcal D}(g)\ge\beta^2/c.$$
--
--   This is the improper learner: it circumvents the NP-hardness of proper learning (Theorem 2) by outputting a polynomial threshold function.
--
--   Differences from the source:
--   - reading: no machine is named → the sampling real RAM `NNPartTree.Machine`; reason: the paper leaves the model open
--   - correction: F any cut class → F has a member of balance at least β; reason: false as printed: for D a point mass every g has bal_D(g) = 0, yet Ω(β²) is claimed
--   - generalization: OPT_β(F) a minimum → an infimum; reason: a minimum need not be attained on an infinite class; when it is, the two agree
--   - reading: inputs β, ε, δ; k(·) the approximation degree of D → k₀ with degree at most k₀ at ε₀ is also an input; reason: without it the statement is false as read: on one D take F₁ = {f₁} of degree 1 and F₂ = {f₂} of large degree, and the same run would have to compete with f₂ by a degree-1 PTF in poly(d) time
--   - reading: log(1/δ) → log(2/δ); reason: at δ → 1, log(1/δ) → 0 would force zero samples; this is the usual meaning of O(log 1/δ)
--   - encoding: a PTF g ∈ P_{k(ε₀)}, probability 1 − δ, O(·), Ω(·) → coefficient vector of degree k₀ in the order of `monomials d k₀`, failure set of outer measure at most δ, absolute c, d ≥ 1; reason: a threshold θ is part of the constant coefficient; on ℝ⁰ no cut is balanced
-- source:
--   Khanna, Padaki, Waingarten, Learning Partition Trees for Nearest Neighbor Search, arXiv:2607.09909 (held copy of 2026-11-03, sha256 d32992f2…), Theorem 3, pp.14–15; proof pp.16–17

import Mathlib
import Definitions.Def_NNPartTree_Learner

open MeasureTheory

namespace NNPartTree

/-- **Theorem 3**, pp.14–15 (corrected). S. Khanna, A. Padaki, E. Waingarten, *Learning Partition Trees for Nearest Neighbor Search*, arXiv:2607.09909 (held copy of 2026-11-03, sha256 d32992f2…).

There is a randomized program PolyCut that, with sample access to `D` and inputs `β ∈ (0, 1/2]`, `ε ∈ (0, 1)`, `δ ∈ (0, 1)`
and `k₀`, uses at most `c (d + k₀)^{k₀} (1/ε² + 1/β⁴) log(2/δ)` samples and `c ((d + k₀)^{k₀} (1/(βε)) log(2/δ))^K` work, on every run;
and if `F` is a cut class with a `β`-balanced member and approximation degree at most `k₀` at `ε₀ = min{ε, β/9}`, then with
probability at least `1 − δ` its output PTF `g` of degree at most `k₀` has `err_D(g) ≤ c √((OPT_β(F) + ε)/β)` and
`bal_D(g) ≥ β²/c`.

**Formalization Note.** Four changes to the page. (1) `F` needs a `β`-balanced member: for `D` a point mass every `g` has
`bal_D(g) = 0`, yet the page claims `Ω(β²)`. (2) `OPT_β(F)` is an infimum, since a minimum need not be attained. (3) `k₀` is an
input, which the printed list omits: otherwise the same run on one `D` would serve `F₁ = {f₁}` of degree `1` and `F₂ = {f₂}` of large
degree, competing with `f₂` by a degree-`1` PTF in `poly(d)` time. (4) `log(1/δ)` becomes `log(2/δ)`: at `δ → 1`, `log(1/δ) → 0` would
force zero samples. The failure set is bounded in outer measure. -/
theorem theorem_3 : ∃ PolyCut : Program, Admissible PolyCut ∧ ∃ c : ℝ, 0 < c ∧ ∃ K : ℕ,
    ∀ (d : ℕ) (β ε δ : ℝ) (k₀ : ℕ), 1 ≤ d → 0 < β → β ≤ 1 / 2 → 0 < ε → ε < 1 → 0 < δ → δ < 1 →
      (∀ ω : (ℕ → Bool) × (ℕ → Pt (2 * d)), ∃ st,
        IsFinal PolyCut (2 * d) (polyCutInput d k₀ β ε δ) ω st ∧
        (st.samplesUsed : ℝ) ≤
          c * (((d : ℝ) + k₀) ^ k₀ * (1 / ε ^ 2 + 1 / β ^ 4) * Real.log (2 / δ)) ∧
        (st.work : ℝ) ≤ c * (((d : ℝ) + k₀) ^ k₀ * (1 / (β * ε)) * Real.log (2 / δ)) ^ K) ∧
      ∀ (D : Measure (Pt d × Pt d)) [IsProbabilityMeasure D] (F : Set (Pt d → ℝ)),
        (∀ f ∈ F, IsCut f) → (∃ f ∈ F, β ≤ bal D f) →
        (∀ f ∈ F, ApproxAt D f (min ε (β / 9)) k₀) →
        sampleSpace D {ω | ¬ ∃ st, IsFinal PolyCut (2 * d) (polyCutInput d k₀ β ε δ) ω st ∧
            err D (outputPTF k₀ st) ≤ c * Real.sqrt ((opt D β F + ε) / β) ∧
            β ^ 2 / c ≤ bal D (outputPTF k₀ st)} ≤
          ENNReal.ofReal δ := by sorry

end NNPartTree
