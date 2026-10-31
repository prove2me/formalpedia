-- Prove2me | Theorems.Thm_MultiUnitProphet_section_5_4_poisson_limit
-- name    : MultiUnitProphet.section_5_4_poisson_limit
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:13:35.433982+00:00
-- url     : https://prove2.me/theorems/8354aae0-0993-4037-a94e-63c1422f428e
-- title:
--   §5.4 — the balanced equal-bias binomials decrease to the Poisson value $\phi_k$
-- statement:
--   Let $k\ge1$ and, for every $n>k$, let $c_n\in[0,1]$ be a bias such that the sum $Y_n$ of $n$ independent Bernoullis of bias $c_n$ has
--
--   $$\mu_k(Y_n)=\delta_k(Y_n)=:\delta_n .$$
--
--   Let $\lambda_k$ be the Poisson rate with $\delta_k(X^{\lambda_k})=\mu_k(X^{\lambda_k})$. Then
--
--   1. $n\mapsto\delta_n$ is non-increasing for $n>k$, and strictly decreasing there when $k\ge2$;
--   2. the means $\lambda_n=\mathbb E[Y_n]=nc_n$ converge to $\lambda_k$;
--   3. $\delta_n\to\delta_k(X^{\lambda_k})=\phi_k$.
--
--   So the balanced binomials converge to the Poisson variable of rate $\lambda_k$, and their common value $\delta_n=\mu_n$ decreases to $\phi_k$.
--
--   Differences from the source:
--   - encoding: a supply k (a positive integer) → k : ℕ with 1 ≤ k; reason: the supply is a positive number of units; at k = 0 the quantities are degenerate
--   - reading: µ_n and δ_n are decreasing functions of n → AntitoneOn on n > k for every k, and StrictAntiOn on n > k for k ≥ 2; reason: at k = 1 the sequence is constant (δ_n = 1/2 for every n), so strict decrease holds exactly for k ≥ 2; both readings of "decreasing" are covered
--   - reading: the limit of {Y_n} is Poisson and µ_n, δ_n converge to µ(Y⋆), δ(Y⋆) with µ(Y⋆) = δ(Y⋆) → n c_n → λ_k and δ_n → δ_k(X^{λ_k}); reason: a Poisson limit with µ = δ has rate λ_k by the uniqueness in eq. (1.1); the means and the value are the quantities used in Lemma 2
--   - reading: µ_n(Y_n) → µ_k(Y_n); reason: the subscript n in µ_n(Y_n) indexes the sequence; the truncation level is the supply k
--   - encoding: a Poisson random variable X^λ with rate λ → deltaPois k λ = Σ_{j<k} e^{−λ}λ^j/j! and muPois k λ = (1/k) Σ_j min{j,k} e^{−λ}λ^j/j!, with λ : ℝ≥0; reason: the Poisson law written through its pmf; same values
--   - encoding: X a sum of independent Bernoullis with biases b_t → deltaPB k b and muPB k b, finite sums over the pmf CommitteeVoting.SingleVoter.pbPMF b univ j, with b t ∈ [0, 1]; reason: the Poisson-binomial law written through its pmf; same values
-- source:
--   Chawla, Devanur & Lykouris, Static pricing for multi-unit prophet inequalities, arXiv:2007.07990v4, §5.4, proof of Lemma 2, p.16 ("We now claim that the quantity Xπ(k,F) in this limit is a Poisson distribution")

import Mathlib
import Definitions.Def_MultiUnitProphet_PoissonBinomial
import Definitions.Def_MultiUnitProphet_Poisson

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace MultiUnitProphet

/-- **§5.4: the balanced equal-bias binomials decrease to the Poisson value `φ_k`.**
Chawla, Devanur & Lykouris, *Static pricing for multi-unit prophet inequalities*,
arXiv:2007.07990v4, §5.4, proof of Lemma 2, p.16: "Let Yn be the sum of n equal Bernoulli distributions with
µn := µn(Yn) = δn(Yn) =: δn. Note that µn and δn are both decreasing functions of n by the above
argument and bounded in [0, 1]. Therefore, they converge to a single limit, µ⋆ = δ⋆. Let λn denote
E[Yn]. We will show that the sequence {λn} converges. Then, by the Poisson limit theorem, the limit
of {Yn}, namely Y⋆ = Xπ(k,F), is Poisson. This means that µn and δn, which are linear functions of
the pdf, also converge to µ(Y⋆) and δ(Y⋆) respectively."

Let `k ≥ 1` and, for every `n > k`, let `c_n ∈ [0, 1]` be a bias such that the sum `Y_n` of `n`
independent Bernoullis of bias `c_n` has `δ_k(Y_n) = µ_k(Y_n) =: δ_n`. Let `λ_k` be the rate with
`δ_k(X^{λ_k}) = µ_k(X^{λ_k})`. Then `n ↦ δ_n` is non-increasing on `n > k`, and strictly
decreasing there when `k ≥ 2`, `λ_n = E[Y_n] = n c_n → λ_k`, and `δ_n → δ_k(X^{λ_k}) = φ_k`.

**Formalization Note.** `µ_n(Y_n)` is `µ_k(Y_n)`. The values `c_n` for `n ≤ k` are irrelevant. At
`k = 1` the sequence is constant (`δ_n = 1/2`), so "decreasing" is strict exactly for `k ≥ 2`. -/
theorem section_5_4_poisson_limit (k : ℕ) (hk : 1 ≤ k) (c : ℕ → ℝ)
    (hc : ∀ n, c n ∈ Set.Icc (0 : ℝ) 1)
    (hbal : ∀ n, k < n → deltaPB k (fun _ : Fin n => c n) = muPB k (fun _ : Fin n => c n))
    (lam : ℝ≥0) (hlam : deltaPois k lam = muPois k lam) :
    AntitoneOn (fun n : ℕ => deltaPB k (fun _ : Fin n => c n)) (Set.Ioi k) ∧
    (2 ≤ k → StrictAntiOn (fun n : ℕ => deltaPB k (fun _ : Fin n => c n)) (Set.Ioi k)) ∧
    Tendsto (fun n : ℕ => (n : ℝ) * c n) atTop (𝓝 (lam : ℝ)) ∧
    Tendsto (fun n : ℕ => deltaPB k (fun _ : Fin n => c n)) atTop (𝓝 (deltaPois k lam)) := by sorry

end MultiUnitProphet
