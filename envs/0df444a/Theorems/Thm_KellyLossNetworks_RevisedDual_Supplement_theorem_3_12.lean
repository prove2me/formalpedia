-- Prove2me | Theorems.Thm_KellyLossNetworks_RevisedDual_Supplement_theorem_3_12
-- name    : KellyLossNetworks.RevisedDual.Supplement.theorem_3_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T02:59:32.422619+00:00
-- url     : https://prove2.me/theorems/afdb8d7b-9a58-46cb-95b7-c2eb8b8bff28
-- title:
--   Theorem 3.12 — under (2.11), (2.12) and 𝒪 = ∅, 1 − L_r(N) = ∏_j (1 − E_j(N))^{A_jr} + o(N^{−1/2})
-- statement:
--   Consider a sequence of loss networks indexed by $N$, with a fixed incidence matrix $A=(A_{jr})$, rates $\nu_r(N)>0$ and capacities $C_j(N)\in\mathbb Z_+$, in the limiting regime (2.11):
--   $$N^{-1}\nu_r(N)\to\nu_r>0,\qquad N^{-1}C_j(N)\to C_j .$$
--   Let $L_r(N)$ be the exact stationary probability that a call requesting route $r$ is lost in the $N$-th network, $1-L_r(N)=G(C(N)-Ae_r)/G(C(N))$ by (1.5).
--   Let $B$ be a solution of maximal support of (2.7) for the limiting data, with busy links $\mathcal B=\{j:B_j>0\}$ and critically loaded links $\mathcal O$, and assume $\mathcal O=\emptyset$. Let $B(N)$ solve (2.7) for the $N$-th network with capacity $C_j(N)$ on $\mathcal B$ and infinite capacity off $\mathcal B$, put $x_r(N)=\nu_r(N)\prod_j(1-B_j(N))^{A_{jr}}$, and assume (2.12):
--   $$C_j(N)-\sum_r A_{jr}x_r(N)=o(N^{1/2}),\qquad j\in\mathcal B.$$
--   Let $E(N)\in[0,1]^J$ be the Erlang fixed point (3.1)–(3.2) of the $N$-th network. Then for every route $r$
--   $$1-L_r(N)=\prod_j\big(1-E_j(N)\big)^{A_{jr}}+o(N^{-1/2}).$$
--
--   Without critically loaded links the Erlang fixed point is accurate to the next order; the paper's Remark 3.13 notes that the restriction $\mathcal O=\emptyset$ cannot be dropped.
--
--   Differences from the source:
--   - encoding: 1 − L_r(N) = P(N) + o(N^{−1/2}) → N^{1/2} · (1 − L_r(N) − P(N)) → 0 as N → ∞; reason: o(N^{−1/2}) is exactly this quantified limit
--   - encoding: rates ν_r(N), ν_r of Poisson streams (implicitly positive) → hypotheses ν_r(N) > 0 for every N and ν_r > 0; reason: standing assumption of the model: the primal problem (2.1) contains log ν_r; the conditions (2.7) and x_r > 0 rely on it
--   - encoding: capacities C_j(N) ∈ ℤ₊, reduced capacities C − Ae_r → CN N : Fin J → ℕ, cast to ℤ; the state space and G are defined for integer capacity vectors; reason: same instances; G(C − Ae_r) = 0 when a coordinate is negative, as in (1.5)
--   - reading: (E_1(N), …, E_J(N)) the Erlang fixed point for the Nth network → any EN with EN N ∈ [0,1]^J solving (3.1)–(3.2) for network N, for all large N; reason: Theorem 3.7 makes the solution unique when every C_j(N) ≥ 1, which holds eventually when C_j > 0; quantifying over all solutions covers the paper's one
--   - reading: B a solution of maximal support of (2.7); B(N) solving (2.7) with C_j(N) on ℬ and ∞ off ℬ; x_r(N) = ν_r(N)∏(1 − B_j(N))^{A_jr} → B with IsMaxSupportSolution; any BN satisfying CenterConditions for all large N (B_j(N) = 0 off ℬ encodes infinite capacity); reason: with infinite capacity the equality case of (2.7) cannot occur, so B_j(N) = 0; x(N) is the same for every such B(N) (Theorem 2.8 for the relaxed network)
-- source:
--   Kelly, Loss networks, Ann. Appl. Probab. 1(3):319–378 (1991), DOI 10.1214/aoap/1177005872, p. 340, Theorem 3.12; (2.11)–(2.12), B(N), x(N) on p. 330; ℬ and 𝒪 on pp. 329–330

import Mathlib
import Definitions.Def_KellyLossNetworks_RevisedDual_Supplement_Exact
import Definitions.Def_KellyLossNetworks_RevisedDual_Supplement_Scaling

open Filter Topology

namespace KellyLossNetworks.RevisedDual.Supplement

/-- **Theorem 3.12.** Under the limiting regime (2.11) and (2.12), and provided `𝒪` is empty,
`1 − L_r(N) = ∏_j (1 − E_j(N))^{A_jr} + o(N^{−1/2})`, `r ∈ ℛ`.

Kelly, Loss networks, Ann. Appl. Probab. 1(3):319–378 (1991), DOI 10.1214/aoap/1177005872,
p. 340, Theorem 3.12; (2.11)–(2.12), `B(N)`, `x(N)` on p. 330; `ℬ`, `𝒪` on pp. 329–330.

**Formalization Note.** `B` is a solution of maximal support of (2.7) for the limiting data,
`ℬ = {j : B_j > 0}`, and `𝒪 = criticalLinks A ν C B`. `BN N` solves (2.7) for the `N`-th
network with capacity `C_j(N)` on `ℬ` and `∞` off `ℬ` (`CenterConditions`), for all large
`N`, and `x_r(N) = ν_r(N) ∏_j (1 − B_j(N))^{A_jr}`. (2.12) is
`(C_j(N) − Σ_r A_jr x_r(N)) / N^{1/2} → 0` for `j ∈ ℬ`. `EN N` is any solution in `[0, 1]^J` of
the Erlang fixed point equations (3.1)–(3.2) of network `N`, for all large `N`.
"`+ o(N^{−1/2})`" is `N^{1/2}` times the difference tending to `0`. -/
theorem theorem_3_12 {J R : ℕ} (A : Fin J → Fin R → ℕ)
    (νN : ℕ → Fin R → ℝ) (CN : ℕ → Fin J → ℕ) (ν : Fin R → ℝ) (C : Fin J → ℝ)
    (hνN : ∀ N r, 0 < νN N r) (hν : ∀ r, 0 < ν r)
    (hrate : ∀ r, Tendsto (fun N : ℕ => νN N r / N) atTop (𝓝 (ν r)))
    (hcap : ∀ j, Tendsto (fun N : ℕ => (CN N j : ℝ) / N) atTop (𝓝 (C j)))
    (B : Fin J → ℝ) (hB : IsMaxSupportSolution A ν C B)
    (hO : criticalLinks A ν C B = ∅)
    (BN : ℕ → Fin J → ℝ)
    (hBN : ∀ᶠ N in atTop, CenterConditions A (νN N) (CN N) {j | 0 < B j} (BN N))
    (h212 : ∀ j, 0 < B j → Tendsto (fun N : ℕ => ((CN N j : ℝ) -
      ∑ r, (A j r : ℝ) * KellyStochasticNetworks.LossLimits.carried A (νN N) (BN N) r) /
        Real.sqrt N) atTop (𝓝 0))
    (EN : ℕ → Fin J → ℝ)
    (hE : ∀ᶠ N in atTop, KellyStochasticNetworks.ErlangFixedPoint A (νN N) (CN N) (EN N) ∧
      ∀ j, EN N j ∈ Set.Icc (0 : ℝ) 1)
    (r : Fin R) :
    Tendsto (fun N : ℕ => Real.sqrt N *
      (acceptance A (νN N) (capInt (CN N)) r - ∏ j, (1 - EN N j) ^ A j r)) atTop (𝓝 0) := by sorry

end KellyLossNetworks.RevisedDual.Supplement
