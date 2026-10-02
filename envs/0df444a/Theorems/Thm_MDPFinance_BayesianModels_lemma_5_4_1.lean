-- Prove2me | Theorems.Thm_MDPFinance_BayesianModels_lemma_5_4_1
-- name    : MDPFinance.BayesianModels.lemma_5_4_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T22:23:40.254032+00:00
-- url     : https://prove2.me/theorems/b3a3e2ba-026f-47ac-8595-b76c69abd36b
-- title:
--   Lemma 5.4.1 — the posterior's explicit $Q_0$-density
-- statement:
--   **Lemma 5.4.1.** The posterior distribution $\mu_n$ of a Bayesian Model has an explicit
--   closed form as a $Q_0$-density: for every history $\tilde h_n = (x_0,a_0,z_1,\dots,x_n)$ and
--   $C \in \mathcal B(\Theta)$,
--   $$
--   \mu_n(C \mid \tilde h_n) =
--   \frac{\int_C \prod_{k=0}^{n-1} q_Z(x_k,\theta,a_k,z_{k+1})\, Q_0(\mathrm d\theta)}
--        {\int_\Theta \prod_{k=0}^{n-1} q_Z(x_k,\theta,a_k,z_{k+1})\, Q_0(\mathrm d\theta)}.
--   $$
--
--   This is Bayes' rule made explicit: the posterior density (relative to the prior $Q_0$) is
--   proportional to the likelihood of the observed disturbances $z_1,\dots,z_n$ given $\theta$.
--
--   **Proof idea (not part of the formalization).** Unrolling `Posterior`'s one-step Bayes update
--   $n$ times from $\mu_0 = Q_0$ telescopes the ratio of one-step likelihoods into the single
--   $n$-fold product shown above.
--
--   **Moderation note.** Stated with Lebesgue integrals, for histories along which the book's quotients are defined: the normalizing constants of the first $n$ updates are finite and the $n$-th is positive (an observed history of positive likelihood). The draft's real Bochner quotient was a default $0$ when the product is not integrable, and undefined ($0/0$) on histories of zero likelihood, where $\mu_n$ is a probability measure nonetheless.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 160, Lemma 5.4.1

import Mathlib
import Definitions.Def_MDPFinance_BayesianModels_Model
import Definitions.Def_MDPFinance_BayesianModels_Posterior

open MeasureTheory ProbabilityTheory

namespace MDPFinance.BayesianModels

/-- Lemma 5.4.1 (Bäuerle–Rieder, p. 160, PDF 173). The posterior distribution `μ_n` has a
`Q_0`-density, i.e. `μ_n(C|h̃_n) = [∫_C ∏_{k=0}^{n-1} q_Z(x_k,θ,a_k,z_{k+1}) Q_0(dθ)] /
[∫_Θ ∏_{k=0}^{n-1} q_Z(x_k,θ,a_k,z_{k+1}) Q_0(dθ)]`, `C ∈ B(Θ)`. Follows from `Posterior`'s
one-step Bayes update `hmu_rec` (this chunk's `Def_..._Posterior`) by induction on `n`: unrolling
`n` applications of the ratio-of-integrals update starting from `μ_0 = Q_0` (`hmu0`) telescopes
into the single `n`-fold-product ratio against `Q_0` stated here. Stated for histories along
which the book's quotients are defined: the normalizing constants of the first `n` updates are
finite and the `n`-th is positive (an observed history of positive likelihood), with Lebesgue
integrals. -/
theorem lemma_5_4_1 {EX Θ A Z : Type*} [MeasurableSpace EX] [MeasurableSpace Θ]
    [MeasurableSpace A] [MeasurableSpace Z] (M : BayesModel EX Θ A Z) (Pf : M.Posterior) (n : ℕ)
    (xs : ℕ → EX) (as : ℕ → A) (zs : ℕ → Z)
    (hfin : ∀ k ≤ n, (∫⁻ θ, ∏ j ∈ Finset.range k,
      ENNReal.ofReal (M.qZ (xs j) θ (as j) (zs (j + 1))) ∂M.Q0) < ⊤)
    (hpos : 0 < ∫⁻ θ, ∏ j ∈ Finset.range n,
      ENNReal.ofReal (M.qZ (xs j) θ (as j) (zs (j + 1))) ∂M.Q0)
    (C : Set Θ) (hC : MeasurableSet C) :
    Pf.mu n xs as zs C =
      (∫⁻ θ in C, ∏ k ∈ Finset.range n, ENNReal.ofReal (M.qZ (xs k) θ (as k) (zs (k + 1))) ∂M.Q0) /
        (∫⁻ θ, ∏ k ∈ Finset.range n, ENNReal.ofReal (M.qZ (xs k) θ (as k) (zs (k + 1))) ∂M.Q0) := by sorry

end MDPFinance.BayesianModels
