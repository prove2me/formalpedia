-- Prove2me | Theorems.Thm_MarkovMixing_cutoff_necessary
-- name    : MarkovMixing.cutoff_necessary
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-22T17:28:07.167835+00:00
-- url     : https://prove2.me/theorems/c931895a-416e-4748-8927-97a6f9d2ad24
-- title:
--   The product condition is necessary for cutoff
-- statement:
--   Consider a family of chains $P^{(n)}$ on finite state spaces, each irreducible and aperiodic, each reversible with respect to its stationary distribution $\pi_n$ (detailed balance $\pi_n(x)P^{(n)}(x,y)=\pi_n(y)P^{(n)}(y,x)$). For each chain: $d_n(t)=\max_x\|P^{(n)t}(x,\cdot)-\pi_n\|_{TV}$ is the worst-case total variation distance, $t^{(n)}_{\mathrm{mix}}(\varepsilon)=\min\{t:d_n(t)\le\varepsilon\}$ with $t^{(n)}_{\mathrm{mix}}=t^{(n)}_{\mathrm{mix}}(1/4)$; among the eigenvalues (real $\lambda$ with $P f=\lambda f$, $f\ne0$), $\lambda_\star$ is the largest absolute value of an eigenvalue $\ne1$, and $t^{(n)}_{\mathrm{rel}}=(1-\lambda_\star)^{-1}$ is the **relaxation time** (Mission VII). The family has a **cutoff** when $t^{(n)}_{\mathrm{mix}}(\varepsilon)/t^{(n)}_{\mathrm{mix}}(1-\varepsilon)\to1$ for every $0<\varepsilon<1$.
--
--   The theorem (Proposition 18.4 of Levin–Peres–Wilmer) asserts: if the mixing times grow to infinity but stay comparable to the relaxation times — $t^{(n)}_{\mathrm{mix}}\le C\,t^{(n)}_{\mathrm{rel}}$ for a fixed constant $C$ — then the family has **no** cutoff.
--
--   The **product condition** $t_{\mathrm{rel}}=o(t_{\mathrm{mix}})$ is therefore necessary for cutoff. The reason: the relaxation-time lower bound of Mission VII gives $t_{\mathrm{mix}}(\varepsilon)\ge(t_{\mathrm{rel}}-1)\log(1/2\varepsilon)$, so if $t_{\mathrm{rel}}$ is proportional to $t_{\mathrm{mix}}$, shrinking $\varepsilon$ inflates $t_{\mathrm{mix}}(\varepsilon)/t_{\mathrm{mix}}$ beyond any bound — an eigenfunction decaying only like $\lambda_\star^t$ keeps the collapse from being abrupt. Whether the product condition is also *sufficient* for reversible families was a famous question of Peres; it fails in general, which makes this necessary direction the definitive elementary statement.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 18.3, Proposition 18.4, p. 252

import Definitions.Def_mm_cutoff

namespace MarkovMixing

/-- **Proposition 18.4** (LPW): a necessary condition for (pre-)cutoff: for
a sequence of reversible irreducible aperiodic chains, if `t_mix/t_rel`
stays bounded, then even the weak cutoff ratio fails — the mixing-time
ratios `t_mix(ε)/t_mix(1−ε)` do not tend to `1` for small `ε`; in
particular the sequence has no cutoff. -/
theorem cutoff_necessary {V : ℕ → Type*} [∀ n, Fintype (V n)]
    [∀ n, DecidableEq (V n)] [∀ n, Nonempty (V n)]
    (P : ∀ n, Matrix (V n) (V n) ℝ) (π : ∀ n, V n → ℝ)
    (hP : ∀ n, IsStochastic (P n)) (hirr : ∀ n, Irreducible (P n))
    (hap : ∀ n, Aperiodic (P n)) (hπ : ∀ n, IsStationary (P n) (π n))
    (hrev : ∀ n, DetailedBalance (P n) (π n))
    (C : ℝ) (hC : 0 < C)
    (hbound : ∀ n, (tMix (P n) (π n) : ℝ) ≤ C * relaxationTime (P n))
    (hgrow : Filter.Tendsto (fun n => tMix (P n) (π n)) Filter.atTop Filter.atTop) :
    ¬HasCutoff P π := by
  sorry

end MarkovMixing
