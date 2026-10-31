-- Prove2me | Theorems.Thm_LPAllocRM_lemma_1
-- name    : LPAllocRM.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:05:12.297825+00:00
-- url     : https://prove2.me/theorems/aa8c1a38-fe83-4133-8023-19c0bd1ff223
-- title:
--   Lemma 1: $h_k(X_k)\to h(X)$ in distribution when $h_k\to h$ uniformly on compacts
-- statement:
--   Let $X_k$ ($k=1,2,\dots$) and $X$ be $\mathbb R^n$-valued random variables, each defined on its own probability space, with $X_k\xrightarrow{\mathcal D}X$. Let $h_k:\mathbb R^n\to\mathbb R$ be measurable functions converging uniformly on compact sets to a continuous function $h:\mathbb R^n\to\mathbb R$. Then
--
--   $$h_k(X_k)\xrightarrow{\mathcal D}h(X).$$
--
--   This extends the continuous mapping theorem to a sequence of functions; it is the tool that turns (7) into the convergence of the normalized revenue in Proposition 1. The paper refers to Billingsley (1968, p. 34) for a proof.
--
--   Differences from the source:
--   - reading: functions h_k : ℝ^n → ℝ → h_k measurable; reason: h_k(X_k) must be a random variable for the conclusion to make sense; the cited source (Billingsley 1968, Thm 5.5) assumes measurable h_k
--   - encoding: X_k →^D X: lim P_k(X_k ∈ S) = P(X ∈ S) for every X-continuity set S (p.723) → Mathlib TendstoInDistribution: weak convergence of the laws, with each X_k almost-everywhere measurable; reason: equivalent by the portmanteau theorem
--   - encoding: a sequence {X_k} → indexed by k : ℕ+, limits along atTop; reason: equivalent to ℕ indexing; matches the problems of §4
-- source:
--   Cooper, Asymptotic Behavior of an Allocation Policy for Revenue Management, Operations Research 50(4) (2002), doi:10.1287/opre.50.4.720.2855, Lemma 1, p.724

import Mathlib
open MeasureTheory Filter

namespace LPAllocRM

/-- Lemma 1 (generalized continuous mapping theorem): if `X_k → X` in distribution for
`ℝ^n`-valued random variables and the functions `h_k : ℝ^n → ℝ` converge uniformly on compact sets
to a continuous `h : ℝ^n → ℝ`, then `h_k(X_k) → h(X)` in distribution.
Cooper, *Asymptotic Behavior of an Allocation Policy for Revenue Management*, Operations Research 50(4) (2002), doi:10.1287/opre.50.4.720.2855,
Lemma 1, p.724 (PDF p.5); "A proof can be found in Billingsley (1968, p. 34)".

**Formalization Note** Each `X_k` lives on its own probability space `(Ω k, P k)`, `X` on
`(Ω', P')`; convergence in distribution is Mathlib's `TendstoInDistribution` (weak convergence of
the laws, equivalent by the portmanteau theorem to the paper's continuity-set definition, p.723). The
sequence is indexed by `k : ℕ+` like the problems; this is equivalent to `ℕ` indexing. Each `h_k` is
assumed measurable, so that `h_k(X_k)` is a random variable, as in Billingsley's Theorem 5.5. -/
theorem lemma_1 {n : ℕ} {Ω : ℕ+ → Type*} [∀ k, MeasurableSpace (Ω k)] {P : ∀ k, Measure (Ω k)}
    [∀ k, IsProbabilityMeasure (P k)] {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {X : ∀ k, Ω k → (Fin n → ℝ)} {X' : Ω' → (Fin n → ℝ)}
    (hX : TendstoInDistribution X atTop X' P P')
    {h : ℕ+ → (Fin n → ℝ) → ℝ} (hmeas : ∀ k, Measurable (h k))
    {hlim : (Fin n → ℝ) → ℝ} (hcont : Continuous hlim)
    (hunif : ∀ K : Set (Fin n → ℝ), IsCompact K → TendstoUniformlyOn h hlim atTop K) :
    TendstoInDistribution (fun k => h k ∘ X k) atTop (hlim ∘ X') P P' := by sorry

end LPAllocRM
