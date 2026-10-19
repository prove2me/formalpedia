-- Prove2me | Theorems.Thm_HTInsensBW_PhaseType_lemma_7
-- name    : HTInsensBW.PhaseType.lemma_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:15:29.863981+00:00
-- url     : https://prove2.me/theorems/ec9d1195-981d-4636-a379-4869fb628fca
-- title:
--   Lemma 7, p. 27 — drift bounds for ‖n‖, positive recurrence and an exponential tail for Σ κ_r N̄_{r,k}
-- statement:
--   Consider a bandwidth-sharing network under the standing assumptions of the paper (0/1 routing matrix of full row rank, every route using a link, positive capacities, weights and base arrival rates, $\boldsymbol\lambda^{(0)}$ on the boundary of the capacity region with $\mathcal L_s\neq\emptyset$, class-$\mathcal D$ file sizes) operated under weighted proportional fairness, and let $\|\cdot\|$ be the norm of (65) and $\mu_{\max}=\max_{r,b}\mu^{(b)}_r$. There are positive constants $A_1,A_3,A_4,\nu,\zeta,\eta_{\min}$ such that for every $0<\epsilon<1$, in the $\epsilon$-th system:
--
--   1. $\Delta\|\mathbf n\|\le-\eta_{\min}A_3\epsilon/\mu_{\max}$ whenever $\|\mathbf n\|\ge\mu_{\max}A_1/(\eta_{\min}A_3\epsilon)$;
--   2. $\Delta\|\mathbf n\|\le\nu\zeta$ for every state $\mathbf n$;
--   3. the flow-count process has a stationary distribution (it is positive recurrent);
--   4. if $\overline{\mathbf N}$ is distributed as a stationary distribution, then for every nonnegative integer $j$
--   $$\mathbb P\Big(\sum_{r,k}\kappa_r\overline N_{r,k}>\frac{\mu_{\max}A_1A_4}{\eta_{\min}A_3\epsilon}+2\nu A_4j\Big)\le\beta^{j+1},\qquad\beta=\frac{\zeta\nu}{\zeta\nu+\epsilon\eta_{\min}A_3/\mu_{\max}}<1 .$$
--
--   Item 3 is what makes the steady-state statements of the mission non-vacuous; item 4 gives finite moments of all orders of the weighted flow count.
--
--   **Formalization Note** The page says "for any nonnegative $\epsilon$ with $\epsilon<1$"; at $\epsilon=0$ the threshold is undefined and the critically loaded chain has no stationary distribution, so $0<\epsilon$ is required. The constants are chosen before $\epsilon$, as the paper's "constant" means independent of the state and of $\epsilon$ (p. 6). The tail bound is asserted for every stationary distribution.
-- source:
--   Wang, Maguluri, Srikant, Ying, Heavy-traffic insensitive bounds for weighted proportionally fair bandwidth sharing policies, arXiv:1808.02120v2, p. 27, Lemma 7; µmax defined on p. 43

import Mathlib
import Definitions.Def_HTInsensBW_PhaseType_Model
import Definitions.Def_HTInsensBW_PhaseType_InnerProduct

namespace HTInsensBW.PhaseType

open Matrix MeasureTheory

/-- **Lemma 7, p. 27 — drift bounds for `‖n‖`, positive recurrence, and an exponential tail for
`Σ_{r,k} κ_r N̄_{r,k}`.** (Wang, Maguluri, Srikant, Ying, Heavy-traffic insensitive bounds for weighted proportionally fair bandwidth sharing policies, arXiv:1808.02120v2, p. 27, Lemma 7; `µ_max` on p. 43.)
There are positive constants `A_1, A_3, A_4, ν, ζ, η_min` such that for every `0 < ε < 1`, in the
`ε`-th system: `Δ‖n‖ ≤ -η_min A_3 ε / µ_max` whenever `‖n‖ ≥ µ_max A_1 / (η_min A_3 ε)`;
`Δ‖n‖ ≤ ν ζ` for all `n`; the flow-count process has a stationary distribution (positive
recurrence); and every stationary distribution satisfies, for every `j ∈ ℕ`,
`P(Σ_{r,k} κ_r N̄_{r,k} > µ_max A_1 A_4/(η_min A_3 ε) + 2 ν A_4 j) ≤ β^{j+1}` with
`β = ζν/(ζν + ε η_min A_3/µ_max)`.

**Formalization Note** The standing hypotheses of §2 and §6 are explicit: `H` has 0/1 entries and full row rank
(p. 5); every route uses at least one link and every capacity is positive (implicit on p. 5 and in
(31): without them the allocation problem (2)–(4) has no optimum); `κ_r > 0` and `λ^(0)_r > 0`
(pp. 5, 7); `λ^(0)` is on the boundary of the capacity region, encoded as (7)–(8):
`Σ_{r : ℓ ∈ r} ρ^(0)_r ≤ C_ℓ` for all links with at least one link critical (`L_s ≠ ∅`); and `x` is
the weighted proportionally fair allocation (2)–(4), as a function of the route totals. The class
`D` (p. 22) is carried by the fields of `PhaseTypeD`.
The page says "for any nonnegative ε with ε < 1"; at `ε = 0` the threshold is undefined and the
chain is not positive recurrent, so `0 < ε` (paper slip). The constants come before `ε` ("a
constant does not depend on either the system state or ε", p. 6). `µ_max = max_{r,b} µ^(b)_r`
(p. 43). Positive recurrence of this irreducible chain is stated as existence of a stationary
distribution; the tail bound is for every stationary distribution. -/
theorem lemma_7 {L R : ℕ} (N : BWNetwork L R)
    (hH01 : ∀ ℓ r, N.H ℓ r = 0 ∨ N.H ℓ r = 1) (hrank : N.H.rank = L)
    (hroute : ∀ r, ∃ ℓ, N.H ℓ r = 1) (hC : ∀ ℓ, 0 < N.C ℓ)
    (hκ : ∀ r, 0 < N.κ r) (hlam0 : ∀ r, 0 < N.lam0 r)
    (hload : ∀ ℓ, ∑ r, N.H ℓ r * routeLoad0 N r ≤ N.C ℓ) (hLs : (critical N).Nonempty)
    (x : (Fin R → ℕ) → Fin R → ℝ) (hx : ∀ m, IsWPFAllocation N m (x m)) :
    ∃ A1 A3 A4 ν ζ ηmin : ℝ, 0 < A1 ∧ 0 < A3 ∧ 0 < A4 ∧ 0 < ν ∧ 0 < ζ ∧ 0 < ηmin ∧
      ∀ ε : ℝ, 0 < ε → ε < 1 →
        (∀ n : State N, muMax N * A1 / (ηmin * A3 * ε) ≤ mNorm N (toReal N n) →
          drift (rates N x ε) (fun n' => mNorm N (toReal N n')) n ≤ -(ηmin * A3 * ε / muMax N)) ∧
        (∀ n : State N, drift (rates N x ε) (fun n' => mNorm N (toReal N n')) n ≤ ν * ζ) ∧
        (∃ π : State N → ℝ, IsStationary (rates N x ε) π) ∧
        ∀ π : State N → ℝ, IsStationary (rates N x ε) π → ∀ j : ℕ,
          ∑' n, (if muMax N * A1 * A4 / (ηmin * A3 * ε) + 2 * ν * A4 * j < wsum N n
            then π n else 0) ≤
            (ζ * ν / (ζ * ν + ε * ηmin * A3 / muMax N)) ^ (j + 1) := by sorry

end HTInsensBW.PhaseType
