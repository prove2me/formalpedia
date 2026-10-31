-- Prove2me | Theorems.Thm_MultiUnitProphet_lemma_7
-- name    : MultiUnitProphet.lemma_7
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:13:29.794405+00:00
-- url     : https://prove2.me/theorems/c8e390c9-d43c-4664-98c6-965bc2d875ec
-- title:
--   Lemma 7 — binomials with means $\varepsilon$ apart have truncated expectations more than $2\varepsilon'$ apart
-- statement:
--   Let $k\ge1$, $\varepsilon>0$, $\lambda,\lambda'\in[0,k]$ with $|\lambda-\lambda'|>\varepsilon$, and $n\ge2k$. Let $\mathrm{Bin}(n,\lambda)$ be the sum of $n$ independent Bernoullis of bias $\lambda/n$ and $\varepsilon':=(1-e^{-\varepsilon/2})/(4k)$. Then
--
--   $$\big|\mu_k(\mathrm{Bin}(n,\lambda))-\mu_k(\mathrm{Bin}(n,\lambda'))\big|>2\varepsilon'.$$
--
--   §5.4 uses it to show that the means $\lambda_n$ of the balanced binomials converge.
--
--   Differences from the source:
--   - encoding: a supply k (a positive integer) → k : ℕ with 1 ≤ k; reason: the supply is a positive number of units; at k = 0 the quantities are degenerate
--   - encoding: λ, λ′ ≤ k → λ, λ′ ∈ [0, k]; reason: λ/n is a Bernoulli bias, so λ ≥ 0 is implicit
--   - reading: ϵ′ := (1 − e^{−ϵ/2})/4k and µ → ϵ′ = (1 − e^{−ϵ/2})/(4k) and µ = µ_k; reason: the denominator is 4k; µ is the truncated expectation µ_k with the same k
--   - encoding: X a sum of independent Bernoullis with biases b_t → deltaPB k b and muPB k b, finite sums over the pmf CommitteeVoting.SingleVoter.pbPMF b univ j, with b t ∈ [0, 1]; reason: the Poisson-binomial law written through its pmf; same values
-- source:
--   Chawla, Devanur & Lykouris, Static pricing for multi-unit prophet inequalities, arXiv:2007.07990v4, Lemma 7, p.16 (proof p.17)

import Mathlib
import Definitions.Def_MultiUnitProphet_PoissonBinomial

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace MultiUnitProphet

/-- **Lemma 7: binomials with separated means have separated truncated expectations.**
Chawla, Devanur & Lykouris, *Static pricing for multi-unit prophet inequalities*,
arXiv:2007.07990v4, Lemma 7, p.16 (proof p.17): "For any ϵ > 0, any λ, λ′ ≤ k with |λ − λ′| > ϵ, and any
n ≥ 2k, define ϵ′ := (1 − e^{−ϵ/2})/4k. Then, it holds that |µ(Bin(n, λ)) − µ(Bin(n, λ′))| > 2ϵ′."
Here `Bin(n, λ)` is "the sum of n Bernoulli variables each with bias λ/n" (p.16) and `µ = µ_k`.

**Formalization Note.** `0 ≤ λ, λ′` so that `λ/n` is a bias; `/4k` is `/(4k)`. -/
theorem lemma_7 (k n : ℕ) (hk : 1 ≤ k) (ε lam lam' : ℝ) (hε : 0 < ε)
    (hlam : lam ∈ Set.Icc (0 : ℝ) k) (hlam' : lam' ∈ Set.Icc (0 : ℝ) k)
    (hdiff : ε < |lam - lam'|) (hn : 2 * k ≤ n) :
    2 * ((1 - Real.exp (-ε / 2)) / (4 * (k : ℝ))) <
      |muPB k (fun _ : Fin n => lam / n) - muPB k (fun _ : Fin n => lam' / n)| := by sorry

end MultiUnitProphet
