-- Prove2me | Theorems.Thm_KellyLossNetworks_RevisedDual_Supplement_theorem_2_30
-- name    : KellyLossNetworks.RevisedDual.Supplement.theorem_2_30
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T02:58:01.374521+00:00
-- url     : https://prove2.me/theorems/cbf0166f-048d-4a00-bf39-90c8d4e27fb1
-- title:
--   Theorem 2.30 — under (2.11)–(2.13), 1 − L_r(N) = ∏_j (1 − b_j(N))^{A_jr} + o(N^{−1/2}) with the β-corrected b(N)
-- statement:
--   Consider a sequence of loss networks indexed by $N$, with a fixed incidence matrix $A=(A_{jr})$, rates $\nu_r(N)>0$ and capacities $C_j(N)\in\mathbb Z_+$, in the limiting regime (2.11):
--   $$N^{-1}\nu_r(N)\to\nu_r>0,\qquad N^{-1}C_j(N)\to C_j .$$
--   Let $L_r(N)$ be the exact stationary probability that a call requesting route $r$ is lost in the $N$-th network, $1-L_r(N)=G(C(N)-Ae_r)/G(C(N))$ by (1.5).
--   Let $B$ be a solution of maximal support of (2.7) for the limiting data, $x_r=\nu_r\prod_j(1-B_j)^{A_{jr}}$, $\mathcal B=\{j:B_j>0\}$ and $\mathcal O$ the critically loaded links. Let $B(N)$ solve (2.7) for the $N$-th network with capacity $C_j(N)$ on $\mathcal B$ and infinite capacity off $\mathcal B$, and $x_r(N)=\nu_r(N)\prod_j(1-B_j(N))^{A_{jr}}$. Assume (2.12) and (2.13):
--   $$C_j(N)-\sum_rA_{jr}x_r(N)=o(N^{1/2}),\ j\in\mathcal B,\qquad C_j(N)-\sum_rA_{jr}x_r(N)=\alpha_jN^{1/2}+o(N^{1/2}),\ j\in\mathcal O.$$
--   Let $u\sim N(0,\Sigma)$, $\Sigma=\operatorname{diag}(x_r)$, conditioned on $A_{\mathcal B}u=0$ and $A_{\mathcal O}u\le\alpha_{\mathcal O}$, and let $\beta\in\mathbb R^J$ satisfy (2.29): $\mathbb E[u_r/x_r]=\sum_j\beta_jA_{jr}$ for all $r$. With $b_j(N)=B_j(N)-N^{-1/2}\beta_j(1-B_j(N))$, for every route $r$
--   $$1-L_r(N)=\prod_j\big(1-b_j(N)\big)^{A_{jr}}+o(N^{-1/2}).$$
--
--   This refines Corollary 2.27 to the next order: acceptance probabilities still factor as if links blocked independently, now with the corrected blocking probabilities $b_j(N)$, including in networks with critically loaded links.
--
--   Differences from the source:
--   - encoding: 1 − L_r(N) = P(N) + o(N^{−1/2}) → N^{1/2} · (1 − L_r(N) − P(N)) → 0 as N → ∞; reason: o(N^{−1/2}) is exactly this quantified limit
--   - encoding: rates ν_r(N), ν_r of Poisson streams (implicitly positive) → hypotheses ν_r(N) > 0 for every N and ν_r > 0; reason: standing assumption of the model: the primal problem (2.1) contains log ν_r; the conditions (2.7) and x_r > 0 rely on it
--   - encoding: capacities C_j(N) ∈ ℤ₊, reduced capacities C − Ae_r → CN N : Fin J → ℕ, cast to ℤ; the state space and G are defined for integer capacity vectors; reason: same instances; G(C − Ae_r) = 0 when a coordinate is negative, as in (1.5)
--   - reading: B a solution of maximal support of (2.7); B(N) solving (2.7) with C_j(N) on ℬ and ∞ off ℬ; x_r(N) = ν_r(N)∏(1 − B_j(N))^{A_jr} → B with IsMaxSupportSolution; any BN satisfying CenterConditions for all large N (B_j(N) = 0 off ℬ encodes infinite capacity); reason: with infinite capacity the equality case of (2.7) cannot occur, so B_j(N) = 0; x(N) is the same for every such B(N) (Theorem 2.8 for the relaxed network)
--   - reading: u formed by conditioning N(0, Σ) on the null event A_ℬu = 0 and on A_𝒪u ≤ α_𝒪 → the mean of the Gaussian density restricted to ker A_ℬ (Haar measure on the subspace) and to the polyhedron A_𝒪u ≤ α_𝒪; reason: the canonical conditional law on the subspace; rank-deficient A_ℬ is allowed, as in the paper
--   - reading: (2.29) holds for some β; b_j(N) built from it → the conclusion for every β satisfying (2.29); reason: β need not be unique when A_ℬ has dependent rows; the paper's choice is one of them
-- source:
--   Kelly, Loss networks, Ann. Appl. Probab. 1(3):319–378 (1991), DOI 10.1214/aoap/1177005872, p. 334, Theorem 2.30; (2.11)–(2.13), B(N), x(N) on p. 330; ℬ, 𝒪 on pp. 329–330; u on p. 331, Σ on p. 332; (2.29) and b_j(N) on p. 334

import Mathlib
import Definitions.Def_KellyLossNetworks_RevisedDual_Supplement_Exact
import Definitions.Def_KellyLossNetworks_RevisedDual_Supplement_Scaling

open Filter Topology

namespace KellyLossNetworks.RevisedDual.Supplement

/-- **Theorem 2.30.** Under the limiting regime (2.11)–(2.13),
`1 − L_r(N) = ∏_j (1 − b_j(N))^{A_jr} + o(N^{−1/2})`, `r ∈ ℛ`,
where `b_j(N) = B_j(N) − N^{−1/2} β_j (1 − B_j(N))` and `β` satisfies (2.29).

Kelly, Loss networks, Ann. Appl. Probab. 1(3):319–378 (1991), DOI 10.1214/aoap/1177005872,
p. 334, Theorem 2.30; (2.11)–(2.13), `B(N)`, `x(N)` on p. 330; `ℬ`, `𝒪` on pp. 329–330; the
conditioned vector `u` on p. 331 and `Σ = diag(x_r)` on p. 332; (2.29) and `b(N)` on p. 334.

**Formalization Note.** `B` is a solution of maximal support of (2.7) for the limiting data,
`x_r = ν_r ∏_j (1 − B_j)^{A_jr}`, `ℬ = {j : B_j > 0}`, `𝒪 = criticalLinks A ν C B`. `BN N` solves
(2.7) for network `N` with capacity `C_j(N)` on `ℬ` and `∞` off `ℬ`, for all large `N`.
(2.12) and (2.13) are stated as limits of `(C_j(N) − Σ_r A_jr x_r(N)) / N^{1/2}` (to `0` on `ℬ`,
to `α_j` on `𝒪`). (2.29) is `𝔼[u_r]/x_r = Σ_j β_j A_jr` for the conditional mean
`conditionalMean` of `u ∼ N(0, diag x)` given `A_ℬ u = 0`, `A_𝒪 u ≤ α_𝒪` (canonical law on the
subspace); `β` is any vector with this property (it need not be unique when `A_ℬ` has
dependent rows). "`+ o(N^{−1/2})`" is `N^{1/2}` times the difference tending to `0`. -/
theorem theorem_2_30 {J R : ℕ} (A : Fin J → Fin R → ℕ)
    (νN : ℕ → Fin R → ℝ) (CN : ℕ → Fin J → ℕ) (ν : Fin R → ℝ) (C : Fin J → ℝ)
    (hνN : ∀ N r, 0 < νN N r) (hν : ∀ r, 0 < ν r)
    (hrate : ∀ r, Tendsto (fun N : ℕ => νN N r / N) atTop (𝓝 (ν r)))
    (hcap : ∀ j, Tendsto (fun N : ℕ => (CN N j : ℝ) / N) atTop (𝓝 (C j)))
    (B : Fin J → ℝ) (hB : IsMaxSupportSolution A ν C B)
    (BN : ℕ → Fin J → ℝ)
    (hBN : ∀ᶠ N in atTop, CenterConditions A (νN N) (CN N) {j | 0 < B j} (BN N))
    (α : Fin J → ℝ)
    (h212 : ∀ j, 0 < B j → Tendsto (fun N : ℕ => ((CN N j : ℝ) -
      ∑ r, (A j r : ℝ) * KellyStochasticNetworks.LossLimits.carried A (νN N) (BN N) r) /
        Real.sqrt N) atTop (𝓝 0))
    (h213 : ∀ j ∈ criticalLinks A ν C B, Tendsto (fun N : ℕ => ((CN N j : ℝ) -
      ∑ r, (A j r : ℝ) * KellyStochasticNetworks.LossLimits.carried A (νN N) (BN N) r) /
        Real.sqrt N) atTop (𝓝 (α j)))
    (β : Fin J → ℝ)
    (hβ : ∀ r, conditionalMean A {j | 0 < B j} (criticalLinks A ν C B)
        (KellyStochasticNetworks.LossLimits.carried A ν B) α r /
          KellyStochasticNetworks.LossLimits.carried A ν B r = ∑ j, β j * (A j r : ℝ))
    (r : Fin R) :
    Tendsto (fun N : ℕ => Real.sqrt N * (acceptance A (νN N) (capInt (CN N)) r -
      ∏ j, (1 - correctedBlocking (BN N) β N j) ^ A j r)) atTop (𝓝 0) := by sorry

end KellyLossNetworks.RevisedDual.Supplement
