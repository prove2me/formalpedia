-- Prove2me | Theorems.Thm_LefebvreVariations_gw_geometric_extinction_half
-- name    : LefebvreVariations.gw_geometric_extinction_half
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T21:25:57.274807+00:00
-- url     : https://prove2.me/theorems/63deb3da-5942-5212-8e6e-e37e2d1c0890
-- title:
--   Lefebvre's variations, No. 163 — on a theme by Galton and Watson: the Galton-Watson process with geometric offspring law of mean 2 goes extinct with probability 1/2
-- statement:
--   A branching process starts from one individual, each individual having independently $k$ children with probability $\tfrac13\left(\tfrac23\right)^k$ for $k=0,1,2,\dots$. Let $Z_n$ be the size of generation $n$. Then
--   $$\mathbb{P}\bigl(\exists n,\ Z_n=0\bigr)=\frac12 .$$
--
--   The offspring generating function is $f(s)=\dfrac{1}{3-2s}$ and the mean is $2$. The equation $f(s)=s$ reads $2s^2-3s+1=0$, with roots $1/2$ and $1$; the extinction probability is the smaller root.
--
--   **Formalization Note** Statement in the platform's own setting `GaltonWatson.extinction_criterion`: `p : PMF ℕ` is the offspring law; `ξ n i` (child count of the `i`-th individual of generation `n`) are measurable, mutually independent with `P (ξ n i ⁻¹' {k}) = p k`; `Z 0 = 1` and `Z (n+1) = ∑_{i<Z n} ξ n i`. The extinction probability is `P.real {ω | ∃ n, Z n ω = 0}`. The offspring law is given by `p k = ENNReal.ofReal ((1/3) * (2/3)^k)` for every `k` (a probability law, since the geometric series sums to `1`); the parent's assumptions `p 1 < 1` and finite mean are not repeated because they follow.
--
--   **Why this is a variation.** Variation of the open platform problem GaltonWatson.extinction_criterion (extinction probability = least root of f(s)=s in [0,1]). This is the geometric offspring law p(k)=(1/3)(2/3)^k, an infinitely supported law with explicit generating function 1/(3-2s), where the least root is 1/2. It follows from the least-root clause of the parent (no formal import: it is a separate statement in the same setting).
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   Parent: GaltonWatson.extinction_criterion (platform, Open), whose source field cites K. B. Athreya and P. E. Ney, Branching Processes, Springer 1972 (Grundlehren 196; the book and its extinction-probability sections exist, bibliographic data checked online), Ch. I Section 5 Thm 1, and G. R. Grimmett and D. R. Stirzaker, Probability and Random Processes, 3rd ed., Oxford 2001, Thm 5.4.5; the theorem numbers are taken from the parent's source field and were not independently verified (cited from memory). For the geometric law p(k)=(1/3)(2/3)^k, f(s)=1/(3-2s) and f(s)=s iff 2s^2-3s+1=0 iff s in {1/2,1}, solved by hand. Numerical check in python3 (iterating f from 0, 2000 steps): 0.5.

import Mathlib

set_option autoImplicit false

namespace LefebvreVariations

open MeasureTheory ProbabilityTheory

/-- Galton–Watson process with geometric offspring law `p(k) = (1/3)(2/3)^k` (mean `2`): `f(s) = 1/(3-2s)`, the extinction probability is `1/2`.
Source: Athreya–Ney, *Branching Processes*, Ch. I §5; Grimmett–Stirzaker, Thm 5.4.5 (both cited from memory). -/
theorem gw_geometric_extinction_half
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (p : PMF ℕ) (hgeom : ∀ k, p k = ENNReal.ofReal ((1 / 3) * (2 / 3) ^ k))
    (ξ : ℕ → ℕ → Ω → ℕ) (hξ_meas : ∀ n i, Measurable (ξ n i))
    (hξ_indep : iIndepFun (fun ni : ℕ × ℕ => ξ ni.1 ni.2) P)
    (hξ_law : ∀ n i k, P (ξ n i ⁻¹' {k}) = p k)
    (Z : ℕ → Ω → ℕ) (hZ0 : ∀ ω, Z 0 ω = 1)
    (hZ : ∀ n ω, Z (n + 1) ω = ∑ i ∈ Finset.range (Z n ω), ξ n i ω) :
    P.real {ω | ∃ n, Z n ω = 0} = 1 / 2 := by
  sorry

end LefebvreVariations
