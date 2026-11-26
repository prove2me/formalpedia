-- Prove2me | Theorems.Thm_LefebvreVariations_gw_critical_binary_extinction_certain
-- name    : LefebvreVariations.gw_critical_binary_extinction_certain
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T21:25:41.228856+00:00
-- url     : https://prove2.me/theorems/1a5b0256-5025-5186-92b2-be5ed1fa49b7
-- title:
--   Lefebvre's variations, No. 200 — on a theme by Galton and Watson: the critical binary Galton-Watson process with offspring law (1/2, 0, 1/2) dies out almost surely
-- statement:
--   A branching process starts from one individual, each individual having independently $0$ or $2$ children with probability $1/2$ each. Let $Z_n$ be the size of generation $n$. Then
--   $$\mathbb{P}\bigl(\exists n,\ Z_n=0\bigr)=1 .$$
--
--   The mean offspring number is exactly $1$ (the critical case) and $f(s)=\tfrac12+\tfrac12 s^2$ has the double root $s=1$ of $f(s)=s$, so extinction is almost sure although the expected population size stays constant.
--
--   **Formalization Note** Statement in the platform's own setting `GaltonWatson.extinction_criterion`: `p : PMF ℕ` is the offspring law; `ξ n i` (child count of the `i`-th individual of generation `n`) are measurable, mutually independent with `P (ξ n i ⁻¹' {k}) = p k`; `Z 0 = 1` and `Z (n+1) = ∑_{i<Z n} ξ n i`. The extinction probability is `P.real {ω | ∃ n, Z n ω = 0}`. The hypotheses on `p` are written as equalities of `ENNReal` values; the parent's assumptions `p 1 < 1` and finite mean are not repeated because they follow.
--
--   **Why this is a variation.** Variation of the open platform problem GaltonWatson.extinction_criterion, whose second half says extinction probability is 1 iff the mean offspring number is at most 1. This is the critical binary case p(0)=p(2)=1/2 (mean exactly 1) in the parent's own setting. It follows from the parent's clause q=1 iff m<=1 (no formal import: it is a separate statement in the same setting).
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   Parent: GaltonWatson.extinction_criterion (platform, Open), whose source field cites K. B. Athreya and P. E. Ney, Branching Processes, Springer 1972 (Grundlehren 196; the book and its extinction-probability sections exist, bibliographic data checked online), Ch. I Section 5 Thm 1, and G. R. Grimmett and D. R. Stirzaker, Probability and Random Processes, 3rd ed., Oxford 2001, Thm 5.4.5; the theorem numbers are taken from the parent's source field and were not independently verified (cited from memory). Here f(s)=1/2+s^2/2, f(s)=s iff (s-1)^2=0, so the only root is 1 (critical case, mean exactly 1, p(1)=0<1). Solved by hand; numerical check in python3 (iterating f from 0, 200000 steps): 0.99999 and still increasing, consistent with convergence to 1 (slowly, as expected in the critical case), not a proof.

import Mathlib

set_option autoImplicit false

namespace LefebvreVariations

open MeasureTheory ProbabilityTheory

/-- Critical binary Galton–Watson process with offspring law `p(0) = p(2) = 1/2` (mean `1`): extinction is almost sure.
Source: Athreya–Ney, *Branching Processes*, Ch. I §5; Grimmett–Stirzaker, Thm 5.4.5 (both cited from memory). -/
theorem gw_critical_binary_extinction_certain
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (p : PMF ℕ) (h0 : p 0 = 1 / 2) (h2 : p 2 = 1 / 2)
    (ξ : ℕ → ℕ → Ω → ℕ) (hξ_meas : ∀ n i, Measurable (ξ n i))
    (hξ_indep : iIndepFun (fun ni : ℕ × ℕ => ξ ni.1 ni.2) P)
    (hξ_law : ∀ n i k, P (ξ n i ⁻¹' {k}) = p k)
    (Z : ℕ → Ω → ℕ) (hZ0 : ∀ ω, Z 0 ω = 1)
    (hZ : ∀ n ω, Z (n + 1) ω = ∑ i ∈ Finset.range (Z n ω), ξ n i ω) :
    P.real {ω | ∃ n, Z n ω = 0} = 1 := by
  sorry

end LefebvreVariations
