-- Prove2me | Theorems.Thm_MDPFinance_POMDPFinance_lemma_6_1_4
-- name    : MDPFinance.POMDPFinance.lemma_6_1_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T22:38:06.816884+00:00
-- url     : https://prove2.me/theorems/db260b80-6a97-4177-81aa-47f34dd1f705
-- title:
--   Lemma 6.1.4 — likelihood-ratio monotonicity of the binomial filter update
-- statement:
--   For the binomial market with unknown up-probability $\theta$, this lemma records the two facts
--   that drive every subsequent monotonicity result of the section. (a) A single down-move followed
--   by an up-move produces a more favorable posterior than a single down-move alone: in terms of the
--   explicit sufficient-statistic update, $\hat p(\cdot\mid m,n+1) \le_{lr} \hat p(\cdot\mid m+1,
--   n+1)$, i.e. observing one more up-move (holding the trial count fixed) shifts the posterior up in
--   the likelihood-ratio order. (b) The belief-only value function $d_k$ (`MDPFinance.POMDPFinance.
--   dPow`) is monotone in the likelihood-ratio order on reachable posteriors: $\rho \le_{lr} \rho'$
--   implies $d_k(\rho) \le d_k(\rho')$ for every $k$.
--
--   **Formalization Note.** Part (a) is stated directly on the explicit posterior-density formula
--   $\hat p(\theta\mid m,n) \propto \theta^m(1-\theta)^{n-m}p_0(\theta)$ (`binomialPosteriorDensity`)
--   rather than through the general filter update $\Phi$, since it is exactly this closed form the
--   book's own proof inspects. Part (b) is stated for arbitrary densities `p`, `p'` in $D_{Q_0}$
--   satisfying the likelihood-ratio hypothesis, turned into measures via `measureOfDensity`
--   (Lebesgue density on $\Theta=(0,1)$), matching the general statement's own universal
--   quantification over $\rho,\rho' \in D_{Q_0}$.
--
--   **Moderation note.** Stated for the binomial market (`IsBinomialMarket`), a prior density $p_0$, $0<d<1+i<u$ and $0<\gamma<1$; part a) is the likelihood ratio order of the two Bayes updates $\Phi(\rho,\bar d)$, $\Phi(\rho,\bar u)$ of the filter (`LRMeasure`), part b) is for the recursion (6.4) `dBin` on normalized posteriors. The draft's part b) quantified over an arbitrary filter market and used unnormalized posterior densities, for which the claim is false.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 179, Lemma 6.1.4

import Mathlib
import Definitions.Def_MDPFinance_POMDPFinance_Filter
import Definitions.Def_MDPFinance_POMDPFinance_Binomial
import Definitions.Def_MDPFinance_POMDPFinance_PowerLogValue

open MeasureTheory ProbabilityTheory

namespace MDPFinance.POMDPFinance

/-- Lemma 6.1.4 (Bäuerle–Rieder, p. 179, PDF 192), for the binomial market with unknown
up-probability `θ \in Θ = (0,1)` (`IsBinomialMarket`: constant hidden parameter, returns `\bar u`
w.p. `θ`, `\bar d` w.p. `1-θ`), prior density `p_0`, up/down factors `0 < d < 1+i < u`,
`\bar u := u/(1+i) - 1`, `\bar d := d/(1+i) - 1`, power utility with `0 < γ < 1` (the subsection's
standing case). For `ρ = \hat μ(\cdot\mid m,n) \in D_{Q_0}` it holds: a) `Φ(ρ,\bar d) \le_{lr}
Φ(ρ,\bar u)`, the likelihood ratio order (Definition B.3.5) of the two Bayes updates of the
filter `Φ` (which, by `FilterOp.hPhi` at the binomial market, are `\hat μ(\cdot\mid m,n+1)` and
`\hat μ(\cdot\mid m+1,n+1)`, the book's proof identity). b) `ρ \le_{lr} ρ' \Rightarrow d_k(\rho)
\le d_k(\rho')` for the binomial recursion (6.4) `dBin` (every `k`, matching the book's own
induction on `n`, restated with `k` = stages remaining; `ρ`, `ρ'` are posterior densities in
`D_{Q_0}`, turned into probability measures via `measureOfDensity`). -/
theorem lemma_6_1_4 (M : FilterMarket ℝ 1) (Fd : FilterOp M) (u dn i : ℝ) (hdn : 0 < dn)
    (hd : dn < 1 + i) (hi : 1 + i < u) (hM : IsBinomialMarket M u dn i) (γ : ℝ) (hγ0 : 0 < γ)
    (hγ1 : γ < 1) (p0 : ℝ → ℝ) (hp0 : IsPriorDensity p0) (m n : ℕ) (hmn : m ≤ n) :
    LRMeasure (volume.restrict (Set.Ioo (0 : ℝ) 1))
        (Fd.Phi (measureOfDensity (binomialPosteriorDensity p0 m n)) (dbar dn i))
        (Fd.Phi (measureOfDensity (binomialPosteriorDensity p0 m n)) (ubar u i)) ∧
      (∀ p p' : ℝ → ℝ, p ∈ DQ0 p0 → p' ∈ DQ0 p0 → LikelihoodRatioOrder p p' →
        ∀ k : ℕ, dBin M Fd u dn i γ k (measureOfDensity p) ≤
          dBin M Fd u dn i γ k (measureOfDensity p')) := by sorry

end MDPFinance.POMDPFinance
