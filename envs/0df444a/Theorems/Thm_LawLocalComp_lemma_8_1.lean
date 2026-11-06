-- Prove2me | Theorems.Thm_LawLocalComp_lemma_8_1
-- name    : LawLocalComp.lemma_8_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:13:37.309582+00:00
-- url     : https://prove2.me/theorems/d939117c-ea5f-4f99-a8f3-3d3ceee26c26
-- title:
--   Lemma 8.1 (Survival geometry)
-- statement:
--   Let $X=b+\Delta K$ be a nonconstant lattice law with positive masses $p_0,\dots,p_h$ whose conditional survival ratios are nonincreasing (in particular a lattice-log-concave law), $S_i=\mathbb P(K\ge i\mid K>0)$ and $f(i)=-\ln S_i$.
--   1. $f$ is convex on its positive domain $\{i\ge1: S_i>0\}$, and $f(1)=0$.
--   2. For integers $1<a<b$ with $S_b>0$,
--   $$\frac ba\le\frac{b-1}{a-1}\le\frac{f(b)}{f(a)}.\tag{33}$$
--   3. $S_{m+j}/S_m\le S_{1+j}$ for $m\ge1$, $j\ge0$ with $S_m>0$.
--   4. With $\nu=\mathbb E[\Delta K\mid K>0]$, for $m\ge1$ with $\mathbb P(K\ge m)>0$ and $s=0,1,\dots$,
--   $$\mathbb E[\Delta(K-m)\mid K\ge m]\le\nu,\qquad\mathbb P(\Delta(K-m)\ge3\nu s\mid K\ge m)\le2^{-s}.\tag{34}$$
--   These are the survival estimates behind the low, high and excess cells of the structured accuracy upper.
--
--   Differences from the source:
--   - generalization: the lattice-log-concave laws of §8 → lattice laws with nonincreasing conditional survival ratios (conditional IFR); reason: every lattice-log-concave law is conditional IFR; Corollary 8.2, p.16: 'Ratios imply Lemma 8.1'
--   - reading: f convex → f(i) − f(i−1) ≤ f(i+1) − f(i) for i ≥ 2 with S_{i+1} > 0; reason: discrete convexity of a function on the integers, on its positive domain
--   - reading: Sm+j/Sm ≤ S1+j and (34), no stated range of m → m ≥ 1 with S_m > 0 (resp. m ≤ h, i.e. P(K ≥ m) > 0); reason: the conditional quantities are defined only there
-- source:
--   Mahboub–Rahgoshay, Optimal Law-Local Compression for Stochastic Loads, STOC 2027 submission (manuscript of Oct. 29, 2026, sha256 5f71501c…aa873), Lemma 8.1, (33)–(34), p.14

import Mathlib
import Definitions.Def_LawLocalComp_IsLatticeRep
import Definitions.Def_LawLocalComp_IsIFRSeq
import Definitions.Def_LawLocalComp_condSurvival
import Definitions.Def_LawLocalComp_activeMean

namespace LawLocalComp

/-- **Lemma 8.1 (Survival geometry).**
Mahboub–Rahgoshay, *Optimal Law-Local Compression for Stochastic Loads*, STOC 2027
submission manuscript of Oct. 29, 2026 (sha256 5f71501c…aa873), Lemma 8.1, (33)–(34), p.14.

For a nonconstant lattice law `X = b + ΔK` with positive masses `p_0, …, p_h` whose conditional survival
ratios are nonincreasing (in particular every lattice-log-concave law), `S_i = P(K ≥ i | K > 0)` and
`f(i) = −ln S_i`: `f` is convex on its positive domain, `f(1) = 0`, and for `1 < a < b` in the positive
domain `b/a ≤ (b − 1)/(a − 1) ≤ f(b)/f(a)` (33). Also `S_{m+j}/S_m ≤ S_{1+j}`, and with
`ν = E[ΔK | K > 0]`, `E[Δ(K − m) | K ≥ m] ≤ ν` and `P(Δ(K − m) ≥ 3νs | K ≥ m) ≤ 2^{−s}` for
`s = 0, 1, …` (34).

**Formalization Note.** Convexity on the integers is `f(i+1) − f(i) ≥ f(i) − f(i−1)` whenever
`S_{i+1} > 0`. The conditional statements are for `m ≥ 1` with `P(K ≥ m) > 0`, i.e. `m ≤ h`. The class
is conditional IFR, which contains the lattice-log-concave laws (Corollary 8.2, p.16: "Ratios imply
Lemma 8.1"). -/
theorem lemma_8_1 (X : Law) (b Δ : ℚ) (h : ℕ) (p : ℕ → ℚ) (hrep : IsLatticeRep X b Δ h p)
    (hIFR : IsIFRSeq h p) (hh : 1 ≤ h) :
    (∀ i : ℕ, 2 ≤ i → 0 < condSurvival h p (i + 1) →
      -Real.log (condSurvival h p i) - -Real.log (condSurvival h p (i - 1)) ≤
        -Real.log (condSurvival h p (i + 1)) - -Real.log (condSurvival h p i)) ∧
    -Real.log (condSurvival h p 1) = 0 ∧
    (∀ a c : ℕ, 1 < a → a < c → 0 < condSurvival h p c →
      (c : ℝ) / a ≤ ((c : ℝ) - 1) / ((a : ℝ) - 1) ∧
        ((c : ℝ) - 1) / ((a : ℝ) - 1) ≤
          -Real.log (condSurvival h p c) / -Real.log (condSurvival h p a)) ∧
    (∀ m j : ℕ, 1 ≤ m → 0 < condSurvival h p m →
      condSurvival h p (m + j) / condSurvival h p m ≤ condSurvival h p (1 + j)) ∧
    (∀ m : ℕ, 1 ≤ m → m ≤ h →
      (Δ : ℝ) * (∑ k ∈ Finset.Icc m h, ((k : ℝ) - m) * p k) / (∑ k ∈ Finset.Icc m h, (p k : ℝ)) ≤
          activeMean X b ∧
        ∀ s : ℕ, (∑ k ∈ (Finset.Icc m h).filter (fun k : ℕ => 3 * activeMean X b * s ≤ (Δ : ℝ) * ((k : ℝ) - m)),
              (p k : ℝ)) /
            (∑ k ∈ Finset.Icc m h, (p k : ℝ)) ≤ (2 : ℝ)⁻¹ ^ s) := by sorry

end LawLocalComp
