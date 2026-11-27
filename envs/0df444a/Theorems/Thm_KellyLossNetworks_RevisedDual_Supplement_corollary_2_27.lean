-- Prove2me | Theorems.Thm_KellyLossNetworks_RevisedDual_Supplement_corollary_2_27
-- name    : KellyLossNetworks.RevisedDual.Supplement.corollary_2_27
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-24T02:58:33.402016+00:00
-- url     : https://prove2.me/theorems/2d6ee906-1312-4d13-87f0-1bad7a7bcd5d
-- title:
--   Corollary 2.27 — under (2.11), 1 − L_r(N) = ∏_j (1 − B_j)^{A_jr} + o(1)
-- statement:
--   Consider a sequence of loss networks indexed by $N$, with a fixed incidence matrix $A=(A_{jr})$, rates $\nu_r(N)>0$ and capacities $C_j(N)\in\mathbb Z_+$, in the limiting regime (2.11):
--   $$N^{-1}\nu_r(N)\to\nu_r>0,\qquad N^{-1}C_j(N)\to C_j .$$
--   Let $L_r(N)$ be the exact stationary probability that a call requesting route $r$ is lost in the $N$-th network, $1-L_r(N)=G(C(N)-Ae_r)/G(C(N))$ by (1.5).
--   Let $B$ be a solution of the conditions (2.7) on $B$ for the limiting rates $\nu$ and capacities $C$. Then for every route $r$
--   $$1-L_r(N)=\prod_j(1-B_j)^{A_{jr}}+o(1)\qquad(N\to\infty).$$
--
--   Asymptotically, calls are accepted as if links blocked independently with the blocking probabilities $B_j$ of the fluid problem; this is statement (1.6) of the introduction. The product does not depend on which solution $B$ of (2.7) is used, since it equals $x_r/\nu_r$ for the unique primal optimum $x$ of Theorem 2.8.
--
--   Differences from the source:
--   - encoding: 1 − L_r(N) = P(N) + o(1) → Tendsto of the difference (or of 1 − L_r(N) to the constant limit) as N → ∞; reason: little-o(1) is exactly convergence of the error to 0
--   - encoding: rates ν_r(N), ν_r of Poisson streams (implicitly positive) → hypotheses ν_r(N) > 0 for every N and ν_r > 0; reason: standing assumption of the model: the primal problem (2.1) contains log ν_r; the conditions (2.7) and x_r > 0 rely on it
--   - encoding: capacities C_j(N) ∈ ℤ₊, reduced capacities C − Ae_r → CN N : Fin J → ℕ, cast to ℤ; the state space and G are defined for integer capacity vectors; reason: same instances; G(C − Ae_r) = 0 when a coordinate is negative, as in (1.5)
--   - reading: B the solution of maximal support fixed in §2.2 → any B solving (2.7) for the limiting ν, C; reason: ∏_j(1 − B_j)^{A_jr} = x_r/ν_r is the same for every solution (Theorem 2.8), so the statement for any solution is the source's
-- source:
--   Kelly, Loss networks, Ann. Appl. Probab. 1(3):319–378 (1991), DOI 10.1214/aoap/1177005872, p. 333, Corollary 2.27; regime (2.11) on p. 330

import Mathlib
import Definitions.Def_KellyLossNetworks_RevisedDual_Supplement_Exact
import Definitions.Def_KellyStochasticNetworks_LossLimits_Optimization

open Filter Topology

namespace KellyLossNetworks.RevisedDual.Supplement

/-- **Corollary 2.27.** Under the limiting regime (2.11),
`1 − L_r(N) = ∏_j (1 − B_j)^{A_jr} + o(1)`.

Kelly, Loss networks, Ann. Appl. Probab. 1(3):319–378 (1991), DOI 10.1214/aoap/1177005872,
p. 333, Corollary 2.27; the regime (2.11) is on p. 330.

**Formalization Note.** The `N`-th network has rates `νN N` and integer capacities `CN N`;
`1 − L_r(N)` is the exact acceptance probability `G(C(N) − Ae_r)/G(C(N))` of (1.5).
`B` is any solution of the conditions (2.7) for the limiting `ν` and `C` (the product
`∏_j (1 − B_j)^{A_jr} = x_r/ν_r` is the same for every solution, Theorem 2.8). "`+ o(1)`" is
convergence of `1 − L_r(N)` to the product. Positive rates `ν_r(N), ν_r > 0` are the standing
assumption of the model (the primal problem (2.1) contains `log ν_r`). -/
theorem corollary_2_27 {J R : ℕ} (A : Fin J → Fin R → ℕ)
    (νN : ℕ → Fin R → ℝ) (CN : ℕ → Fin J → ℕ) (ν : Fin R → ℝ) (C : Fin J → ℝ)
    (hνN : ∀ N r, 0 < νN N r) (hν : ∀ r, 0 < ν r)
    (hrate : ∀ r, Tendsto (fun N : ℕ => νN N r / N) atTop (𝓝 (ν r)))
    (hcap : ∀ j, Tendsto (fun N : ℕ => (CN N j : ℝ) / N) atTop (𝓝 (C j)))
    (B : Fin J → ℝ) (hB : KellyStochasticNetworks.LossLimits.blockingConditions A ν C B)
    (r : Fin R) :
    Tendsto (fun N : ℕ => acceptance A (νN N) (capInt (CN N)) r) atTop
      (𝓝 (∏ j, (1 - B j) ^ A j r)) := by sorry

end KellyLossNetworks.RevisedDual.Supplement
