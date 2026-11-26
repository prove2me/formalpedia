-- Prove2me | Theorems.Thm_LefebvreVariations_gw_binary_extinction_one_third
-- name    : LefebvreVariations.gw_binary_extinction_one_third
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T21:25:23.662077+00:00
-- url     : https://prove2.me/theorems/5ad525ab-6769-4712-ac0b-7a012b400fbb
-- title:
--   Lefebvre's variations, No. 160 — on a theme by Galton and Watson: the Galton-Watson process with offspring law (1/4, 0, 3/4) goes extinct with probability 1/3
-- statement:
--   A branching process starts from one individual, each individual having independently $0$ children with probability $1/4$ and $2$ children with probability $3/4$. Let $Z_n$ be the size of generation $n$. Then
--   $$\mathbb{P}\bigl(\exists n,\ Z_n=0\bigr)=\frac13 .$$
--
--   The offspring generating function is $f(s)=\tfrac14+\tfrac34 s^2$, whose roots of $f(s)=s$ in $[0,1]$ are $1/3$ and $1$; the extinction probability is the smaller one because the mean offspring number is $3/2>1$.
--
--   **Formalization Note** Statement in the platform's own setting `GaltonWatson.extinction_criterion`: `p : PMF ℕ` is the offspring law; `ξ n i` (child count of the `i`-th individual of generation `n`) are measurable, mutually independent with `P (ξ n i ⁻¹' {k}) = p k`; `Z 0 = 1` and `Z (n+1) = ∑_{i<Z n} ξ n i`. The extinction probability is `P.real {ω | ∃ n, Z n ω = 0}`. The hypotheses on `p` are written as equalities of `ENNReal` values; the parent's assumptions `p 1 < 1` and finite mean are not repeated because they follow.
--
--   **Why this is a variation.** Variation of the open platform problem GaltonWatson.extinction_criterion (extinction probability is the least root of f(s)=s in [0,1], and equals 1 iff the mean is at most 1). It is the first non-degenerate supercritical case, the binary offspring law with p(0)=1/4 and p(2)=3/4, in the parent's own setting; the value 1/3 is the smaller root of f(s)=s. It follows from the least-root clause of the parent (no formal import: it is a separate statement in the same setting).
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   Parent: GaltonWatson.extinction_criterion (platform, Open), whose source field cites K. B. Athreya and P. E. Ney, Branching Processes, Springer 1972 (Grundlehren 196; the book and its extinction-probability sections exist, bibliographic data checked online), Ch. I Section 5 Thm 1, and G. R. Grimmett and D. R. Stirzaker, Probability and Random Processes, 3rd ed., Oxford 2001, Thm 5.4.5; the theorem numbers are taken from the parent's source field and were not independently verified (cited from memory). The value is the smallest root in [0,1] of f(s)=s, f(s)=1/4+3s^2/4: 3s^2-4s+1=0 iff s in {1/3,1}, solved by hand. Numerical check in python3 (iterating f from 0, 2000 steps): 0.33333333333333, matching 1/3.

import Mathlib

set_option autoImplicit false

namespace LefebvreVariations

open MeasureTheory ProbabilityTheory

/-- Galton–Watson process with offspring law `p(0) = 1/4`, `p(2) = 3/4` (mean `3/2`): the extinction probability is `1/3`, the smaller root of `f(s) = 1/4 + 3s²/4 = s`, as in the extinction criterion.
Source: Athreya–Ney, *Branching Processes*, Ch. I §5; Grimmett–Stirzaker, Thm 5.4.5 (both cited from memory). -/
theorem gw_binary_extinction_one_third
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (p : PMF ℕ) (h0 : p 0 = 1 / 4) (h2 : p 2 = 3 / 4)
    (ξ : ℕ → ℕ → Ω → ℕ) (hξ_meas : ∀ n i, Measurable (ξ n i))
    (hξ_indep : iIndepFun (fun ni : ℕ × ℕ => ξ ni.1 ni.2) P)
    (hξ_law : ∀ n i k, P (ξ n i ⁻¹' {k}) = p k)
    (Z : ℕ → Ω → ℕ) (hZ0 : ∀ ω, Z 0 ω = 1)
    (hZ : ∀ n ω, Z (n + 1) ω = ∑ i ∈ Finset.range (Z n ω), ξ n i ω) :
    P.real {ω | ∃ n, Z n ω = 0} = 1 / 3 := by
  sorry

end LefebvreVariations
