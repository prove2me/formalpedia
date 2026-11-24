-- Prove2me | Theorems.Thm_KellyLossNetworks_RevisedDual_Supplement_theorem_3_11
-- name    : KellyLossNetworks.RevisedDual.Supplement.theorem_3_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T02:59:01.263687+00:00
-- url     : https://prove2.me/theorems/3af1f6db-2899-4ead-a26c-61ca62cafa27
-- title:
--   Theorem 3.11 — under (2.11), 1 − L_r(N) = ∏_j (1 − E_j(N))^{A_jr} + o(1) for the Erlang fixed point E(N)
-- statement:
--   Consider a sequence of loss networks indexed by $N$, with a fixed incidence matrix $A=(A_{jr})$, rates $\nu_r(N)>0$ and capacities $C_j(N)\in\mathbb Z_+$, in the limiting regime (2.11):
--   $$N^{-1}\nu_r(N)\to\nu_r>0,\qquad N^{-1}C_j(N)\to C_j .$$
--   Let $L_r(N)$ be the exact stationary probability that a call requesting route $r$ is lost in the $N$-th network, $1-L_r(N)=G(C(N)-Ae_r)/G(C(N))$ by (1.5).
--   Let $(E_1(N),\dots,E_J(N))\in[0,1]^J$ be the Erlang fixed point of the $N$-th network, i.e. a solution of
--   $$E_j=E(\rho_j,C_j(N)),\qquad \rho_j=(1-E_j)^{-1}\sum_r A_{jr}\nu_r(N)\prod_i(1-E_i)^{A_{ir}},$$
--   with $E$ Erlang's formula (1.1). Then for every route $r$
--   $$1-L_r(N)=\prod_j\big(1-E_j(N)\big)^{A_{jr}}+o(1)\qquad(N\to\infty).$$
--
--   The Erlang fixed point approximation is thus asymptotically exact for the acceptance probabilities in the regime where capacities and loads grow together.
--
--   **Formalization Note** The Erlang fixed point equations are the published `KellyStochasticNetworks.ErlangFixedPoint`; the theorem applies to any sequence of solutions in $[0,1]^J$ for all large $N$.
--
--   Differences from the source:
--   - encoding: 1 − L_r(N) = P(N) + o(1) → Tendsto of the difference (or of 1 − L_r(N) to the constant limit) as N → ∞; reason: little-o(1) is exactly convergence of the error to 0
--   - encoding: rates ν_r(N), ν_r of Poisson streams (implicitly positive) → hypotheses ν_r(N) > 0 for every N and ν_r > 0; reason: standing assumption of the model: the primal problem (2.1) contains log ν_r; the conditions (2.7) and x_r > 0 rely on it
--   - encoding: capacities C_j(N) ∈ ℤ₊, reduced capacities C − Ae_r → CN N : Fin J → ℕ, cast to ℤ; the state space and G are defined for integer capacity vectors; reason: same instances; G(C − Ae_r) = 0 when a coordinate is negative, as in (1.5)
--   - reading: (E_1(N), …, E_J(N)) the Erlang fixed point for the Nth network → any EN with EN N ∈ [0,1]^J solving (3.1)–(3.2) for network N, for all large N; reason: Theorem 3.7 makes the solution unique when every C_j(N) ≥ 1, which holds eventually when C_j > 0; quantifying over all solutions covers the paper's one
-- source:
--   Kelly, Loss networks, Ann. Appl. Probab. 1(3):319–378 (1991), DOI 10.1214/aoap/1177005872, p. 340, Theorem 3.11; regime (2.11) on p. 330; Erlang fixed point (3.1)–(3.2) on p. 337 and for network N on p. 339

import Mathlib
import Definitions.Def_KellyLossNetworks_RevisedDual_Supplement_Exact
import Definitions.Def_KellyStochasticNetworks_LossLimits_Optimization

open Filter Topology

namespace KellyLossNetworks.RevisedDual.Supplement

/-- **Theorem 3.11.** Under the limiting regime (2.11),
`1 − L_r(N) = ∏_j (1 − E_j(N))^{A_jr} + o(1)`, `r ∈ ℛ`, where `(E_1(N), …, E_J(N))` is the
Erlang fixed point (3.1)–(3.2) of the `N`-th network.

Kelly, Loss networks, Ann. Appl. Probab. 1(3):319–378 (1991), DOI 10.1214/aoap/1177005872,
p. 340, Theorem 3.11; the regime (2.11) is on p. 330, the Erlang fixed point for network `N`
on p. 339.

**Formalization Note.** `1 − L_r(N)` is the exact acceptance probability (1.5) of the `N`-th
network. `EN N` is any solution in `[0, 1]^J` of the published Erlang fixed point equations
`KellyStochasticNetworks.ErlangFixedPoint` (which are (3.1)–(3.2)) for the `N`-th network,
required for all large `N` (by Theorem 3.7 the solution exists and is unique once every
`C_j(N) ≥ 1`). "`+ o(1)`" is convergence of the difference to `0`. Positive rates are the
standing assumption of the model. No second-order, rank or noncritical-link condition is
added, and no fluid blocking-solution existence is assumed. -/
theorem theorem_3_11 {J R : ℕ} (A : Fin J → Fin R → ℕ)
    (νN : ℕ → Fin R → ℝ) (CN : ℕ → Fin J → ℕ) (ν : Fin R → ℝ) (C : Fin J → ℝ)
    (hνN : ∀ N r, 0 < νN N r) (hν : ∀ r, 0 < ν r)
    (hrate : ∀ r, Tendsto (fun N : ℕ => νN N r / N) atTop (𝓝 (ν r)))
    (hcap : ∀ j, Tendsto (fun N : ℕ => (CN N j : ℝ) / N) atTop (𝓝 (C j)))
    (EN : ℕ → Fin J → ℝ)
    (hE : ∀ᶠ N in atTop, KellyStochasticNetworks.ErlangFixedPoint A (νN N) (CN N) (EN N) ∧
      ∀ j, EN N j ∈ Set.Icc (0 : ℝ) 1)
    (r : Fin R) :
    Tendsto (fun N : ℕ => acceptance A (νN N) (capInt (CN N)) r - ∏ j, (1 - EN N j) ^ A j r)
      atTop (𝓝 0) := by sorry

end KellyLossNetworks.RevisedDual.Supplement
