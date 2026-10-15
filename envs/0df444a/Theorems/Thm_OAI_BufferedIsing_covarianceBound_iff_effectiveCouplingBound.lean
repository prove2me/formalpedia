-- Prove2me | Theorems.Thm_OAI_BufferedIsing_covarianceBound_iff_effectiveCouplingBound
-- name    : OAI.BufferedIsing.covarianceBound_iff_effectiveCouplingBound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T22:19:13.236703+00:00
-- url     : https://prove2.me/theorems/108523de-3415-4cfb-8d79-8781ac2d69c3
-- title:
--   Arbitrary-field covariance bound is equivalent to maximality of the zero-field effective coupling
-- statement:
--   Consider finite graphs $G$ on vertex sets $V=\{0,\dots,n-1\}$ with $m$ separately indexed edges $e$, endpoints $\ell(e)\neq r(e)$ and ferromagnetic couplings $K_e\ge0$, together with external fields $h\in\mathbb{R}^V$. The Gibbs weight of $\sigma\in\{-1,+1\}^V$ is $w_h(\sigma)=\exp\big(\sum_eK_e\sigma_{\ell(e)}\sigma_{r(e)}+\sum_vh_v\sigma_v\big)$ and $\langle f\rangle_{G,h}=\sum_\sigma w_h(\sigma)f(\sigma)\big/\sum_\sigma w_h(\sigma)$. For sites $u,v$ the two-site table is $T^{G,h}_{uv}(s,t)=\sum_{\sigma}\mathbf 1[\sigma_u=s,\ \sigma_v=t]\,w_h(\sigma)$ for $s,t\in\{-1,+1\}$, and the *effective coupling* of a $2\times2$ table $w$ is
--   $$
--   \mathcal K(w)=\tfrac14\big(\log w(+,+)+\log w(-,-)-\log w(+,-)-\log w(-,+)\big).
--   $$
--   Consider the following two statements.
--
--   **(A) Arbitrary-field covariance bound.** For all $n,m$, every such graph $G$, every field $h\in\mathbb{R}^V$ and all sites $u,v\in V$ (the case $u=v$ included),
--   $$
--   \langle\sigma_u\sigma_v\rangle_{G,h}-\langle\sigma_u\rangle_{G,h}\langle\sigma_v\rangle_{G,h}\le\langle\sigma_u\sigma_v\rangle_{G,0}.
--   $$
--
--   **(B) Effective coupling bound.** For all $n,m$, every such graph $G$, every field $h\in\mathbb{R}^V$ and all distinct sites $u\neq v$,
--   $$
--   \mathcal K\big(T^{G,h}_{uv}\big)\le\mathcal K\big(T^{G,0}_{uv}\big).
--   $$
--
--   **Theorem.** Statement (A) holds if and only if statement (B) holds.
--
--   Statement (A) says that under any external field, with arbitrary signs, the spin covariance of two sites is at most their zero-field correlation; (B) says that external fields never increase the effective interaction between two sites, measured by the log-odds ratio of their joint marginal. The equivalence transports a covariance inequality to effective couplings, which are insensitive to fields acting on the two sites themselves and therefore combine well with pinning and contraction of vertex sets.
--
--   **Formalization Note** (A) and (B) are the propositions `ArbitraryFieldCovarianceBound` and `EffectiveCouplingBound`, each quantifying over all `n m : ℕ`, all `G : FiniteGraph n m`, all fields and all sites. $\mathcal K$ is `tableCoupling` and $T^{G,h}_{uv}$ is `pairTable (weight G h) u v`; for $u\neq v$ all four entries are positive, so the logarithms are of positive numbers.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Ising/Covariance.lean#L209-L231

import Mathlib
import Definitions.Def_BufferedIsing
import Definitions.Def_OAI_Probability_Ising_Basic
import Definitions.Def_OAI_Probability_Ising_Colorings
import Definitions.Def_OAI_Probability_Ising_EdwardsSokal
import Definitions.Def_OAI_Probability_Ising_TwoSpin
import Definitions.Def_OAI_Probability_Ising_SpinCorrelation
import Definitions.Def_OAI_Probability_Ising_Marginals
import Definitions.Def_OAI_Probability_Ising_PinnedMarginal
import Definitions.Def_OAI_Probability_Ising_Covariance

open OAI OAI.BufferedIsing
open scoped BigOperators Classical

theorem OAI.BufferedIsing.covarianceBound_iff_effectiveCouplingBound :
    ArbitraryFieldCovarianceBound ↔ EffectiveCouplingBound := by sorry
