-- Prove2me | Theorems.Thm_KallMayerSLP_Bonferroni_eq_3_16_hunter_bound
-- name    : KallMayerSLP.Bonferroni.eq_3_16_hunter_bound
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:13:21.153412+00:00
-- url     : https://prove2.me/theorems/fdd8401b-0a95-4479-817e-639d83d42457
-- title:
--   Hunter's upper bound on the probability of a union
-- statement:
--   For events $B_1,\dots,B_r$, $r\ge1$, on a probability space, and any choice of indices $[j]\in\{1,\dots,j-1\}$, $j=2,\dots,r$,
--   $$
--   \begin{aligned}
--   \mathbb P(B_1\cup\dots\cup B_r)
--   &=\mathbb P(B_1)+\sum_{j=2}^r\mathbb P(B_1^c\cap\dots\cap B_{j-1}^c\cap B_j)\\
--   &\le\mathbb P(B_1)+\sum_{j=2}^r\mathbb P(B_{[j]}^c\cap B_j)\\
--   &=\sum_{j=1}^r\mathbb P(B_j)-\sum_{j=2}^r\mathbb P(B_{[j]}\cap B_j).
--   \end{aligned}
--   $$
--   The bound improves the union bound using pairwise intersections.
--
--   Differences from the source:
--   - encoding: events $B_1,\dots,B_r$ (or variables $v_1,\dots,v_r$) indexed by $1,\dots,r$ → indexed by `Fin r`, that is by $0,\dots,r-1$; reason: Lean convention; same instances
--   - encoding: the number $r$ of events $B_1,\dots,B_r$ (the dimension of $\xi$ with values in $\mathbb R^r$) is left implicit → hypothesis `1 ≤ r`; reason: the family $B_1,\dots,B_r$ starts at $B_1$, so the book has $r\ge1$; the hypothesis excludes only the empty family
--   - encoding: a choice of $[j]$ for $j=2,\dots,r$ → a function `parent : Fin r → Fin r` constrained only at $j$ with $0<j$; reason: the value at the first index is never used
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 4, §3.4, eq. (3.16), p.290 (PDF 299)

import Mathlib

open MeasureTheory

namespace KallMayerSLP.Bonferroni

/-- Hunter's bound: for any choice of indices `[j] ∈ {1, …, j - 1}`, `j = 2, …, r`,
`ℙ(B₁ ∪ ⋯ ∪ B_r) = ℙ(B₁) + ∑_{j=2}^r ℙ(B₁^c ∩ ⋯ ∩ B_{j-1}^c ∩ B_j)
  ≤ ℙ(B₁) + ∑_{j=2}^r ℙ(B_{[j]}^c ∩ B_j) = ∑_{j=1}^r ℙ(B_j) - ∑_{j=2}^r ℙ(B_{[j]} ∩ B_j)`.

Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 4, eq. (3.16), p.290 (PDF 299).

**Formalization Note.** The book's index `1` is `⟨0, hr⟩ : Fin r`, and `j = 2, …, r` is the set of
`j : Fin r` with `0 < (j : ℕ)`. The choice `[·]` is a function `parent : Fin r → Fin r` of which only
the values at those `j` are used, with `parent j < j`. -/
theorem eq_3_16_hunter_bound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {r : ℕ} (hr : 1 ≤ r) (B : Fin r → Set Ω) (hB : ∀ i, MeasurableSet (B i))
    (parent : Fin r → Fin r) (hparent : ∀ j : Fin r, 0 < (j : ℕ) → parent j < j) :
    μ.real (⋃ i, B i) =
        μ.real (B ⟨0, hr⟩) +
          ∑ j ∈ Finset.univ.filter (fun j : Fin r => 0 < (j : ℕ)),
            μ.real ((⋂ i, ⋂ (_ : i < j), (B i)ᶜ) ∩ B j) ∧
      μ.real (B ⟨0, hr⟩) +
          ∑ j ∈ Finset.univ.filter (fun j : Fin r => 0 < (j : ℕ)),
            μ.real ((⋂ i, ⋂ (_ : i < j), (B i)ᶜ) ∩ B j) ≤
        μ.real (B ⟨0, hr⟩) +
          ∑ j ∈ Finset.univ.filter (fun j : Fin r => 0 < (j : ℕ)),
            μ.real ((B (parent j))ᶜ ∩ B j) ∧
      μ.real (B ⟨0, hr⟩) +
          ∑ j ∈ Finset.univ.filter (fun j : Fin r => 0 < (j : ℕ)),
            μ.real ((B (parent j))ᶜ ∩ B j) =
        ∑ j, μ.real (B j) -
          ∑ j ∈ Finset.univ.filter (fun j : Fin r => 0 < (j : ℕ)),
            μ.real (B (parent j) ∩ B j) := by sorry

end KallMayerSLP.Bonferroni
