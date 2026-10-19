-- Prove2me | Theorems.Thm_HTInsensBW_PhaseType_theorem_4
-- name    : HTInsensBW.PhaseType.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:14:39.2556+00:00
-- url     : https://prove2.me/theorems/141ba03f-6a19-4ee1-9dd8-a0d5c408fd83
-- title:
--   Theorem 4, p. 25 — under phase-type file sizes the weighted mean flow count is between Ls·min κ/ϵ and Ls·max κ/ϵ up to o(1/ϵ)
-- statement:
--   Consider a bandwidth-sharing network with links $\ell=1,\dots,L$ of capacities $C_\ell>0$ and routes $r=1,\dots,R$, whose $0/1$ routing matrix $H$ has full row rank and in which every route uses at least one link. Flows arrive on route $r$ as a Poisson process of rate $\lambda^{(\epsilon)}_r=(1-\epsilon)\lambda^{(0)}_r$ with $\lambda^{(0)}_r>0$, and their file sizes have a phase-type law $(\pi_r,S_r)$ in the class $\mathcal D$, of mean $1/\mu_r$. The vector $\boldsymbol\lambda^{(0)}$ lies on the boundary of the capacity region: with $\rho^{(0)}_r=\lambda^{(0)}_r/\mu_r$,
--   $$\sum_{r:\ell\in r}\rho^{(0)}_r\le C_\ell\ \text{ for every link},\qquad\mathcal L_s=\Big\{\ell:\sum_{r:\ell\in r}\rho^{(0)}_r=C_\ell\Big\}\neq\emptyset ,$$
--   and $L_s=|\mathcal L_s|$. Bandwidth is shared by the weighted proportionally fair policy with weights $\kappa_1,\dots,\kappa_R>0$. Let $\overline{\mathbf N}^{(\epsilon)}$ be distributed as the stationary distribution of the flow-count process of the $\epsilon$-th system, $0<\epsilon<1$. Then, as $\epsilon\to0^+$,
--   $$\frac{L_s\cdot\min_r\kappa_r}{\epsilon}+o\Big(\frac1\epsilon\Big)\ \le\ \mathbb E\Big[\sum_r\kappa_r\overline N^{(\epsilon)}_r\Big]\ \le\ \frac{L_s\cdot\max_r\kappa_r}{\epsilon}+o\Big(\frac1\epsilon\Big).$$
--   Precisely: for every $\delta>0$ there is $\epsilon_1>0$ such that for every $0<\epsilon<\epsilon_1$ and every stationary distribution, the expectation is finite and lies between $(L_s\min_r\kappa_r-\delta)/\epsilon$ and $(L_s\max_r\kappa_r+\delta)/\epsilon$.
--
--   The leading terms do not depend on the file-size laws within $\mathcal D$ (not even on their means), which is what makes the bounds heavy-traffic insensitive; for equal weights they coincide and give the exact heavy-traffic limit $L_s/\epsilon$.
--
--   **Formalization Note** The flow-count process is the phase-level Markov chain (58)–(60), encoded with zero diagonal rates; "stationary distribution" means a nonnegative, total-mass-one solution of the global balance equations, and the statement covers every such solution (existence is Lemma 7). $o(1/\epsilon)$ is the $\epsilon$–$\delta$ statement above, with $\epsilon_1$ depending only on $\delta$ and the network. The boundary of the capacity region is encoded by (7)–(8) with at least one critical link. "Every route uses a link" and "$C_\ell>0$" are implicit in the paper and stated explicitly. The allocation is any function of the route counts satisfying the optimality conditions (2)–(4) (it exists and is unique, by (5)).
-- source:
--   Wang, Maguluri, Srikant, Ying, Heavy-traffic insensitive bounds for weighted proportionally fair bandwidth sharing policies, arXiv:1808.02120v2, p. 25, Theorem 4

import Mathlib
import Definitions.Def_HTInsensBW_PhaseType_Model

namespace HTInsensBW.PhaseType

/-- **Theorem 4, p. 25 — bounds on flow counts (heavy-traffic insensitivity).**
(Wang, Maguluri, Srikant, Ying, Heavy-traffic insensitive bounds for weighted proportionally fair bandwidth sharing policies, arXiv:1808.02120v2, p. 25, Theorem 4.)
Consider a bandwidth-sharing network with class-`D` phase-type file sizes, Poisson arrivals at
rates `λ^(ε) = (1 - ε) λ^(0)` where `λ^(0)` critically loads the set `L_s` of `L_s` links, and the
weighted proportionally fair policy with weights `κ_1, …, κ_R`. Let `N̄^(ε)` be distributed as the
stationary distribution of the flow-count process. Then, as `ε → 0+`,
`L_s min_r κ_r / ε + o(1/ε) ≤ E[Σ_r κ_r N̄^(ε)_r] ≤ L_s max_r κ_r / ε + o(1/ε)`.

**Formalization Note** The standing hypotheses of §2 and §6 are explicit: `H` has 0/1 entries and full row rank
(p. 5); every route uses at least one link and every capacity is positive (implicit on p. 5 and in
(31): without them the allocation problem (2)–(4) has no optimum); `κ_r > 0` and `λ^(0)_r > 0`
(pp. 5, 7); `λ^(0)` is on the boundary of the capacity region, encoded as (7)–(8):
`Σ_{r : ℓ ∈ r} ρ^(0)_r ≤ C_ℓ` for all links with at least one link critical (`L_s ≠ ∅`); and `x` is
the weighted proportionally fair allocation (2)–(4), as a function of the route totals. The class
`D` (p. 22) is carried by the fields of `PhaseTypeD`.
`o(1/ε)` is the `ε`–`δ` statement: for every `δ > 0` there is `ε_1 > 0` (depending only on `δ` and
the network) such that for all `0 < ε < ε_1` and every stationary distribution `π`,
`(L_s κ_min - δ)/ε ≤ E_π[Σ_r κ_r N_r] ≤ (L_s κ_max + δ)/ε`, and the expectation is finite.
"the stationary distribution" is read as every stationary distribution; existence is Lemma 7. The
flow-count process is the phase-level CTMC (58)–(60), with zero diagonal rates. -/
theorem theorem_4 {L R : ℕ} (N : BWNetwork L R)
    (hH01 : ∀ ℓ r, N.H ℓ r = 0 ∨ N.H ℓ r = 1) (hrank : N.H.rank = L)
    (hroute : ∀ r, ∃ ℓ, N.H ℓ r = 1) (hC : ∀ ℓ, 0 < N.C ℓ)
    (hκ : ∀ r, 0 < N.κ r) (hlam0 : ∀ r, 0 < N.lam0 r)
    (hload : ∀ ℓ, ∑ r, N.H ℓ r * routeLoad0 N r ≤ N.C ℓ) (hLs : (critical N).Nonempty)
    (x : (Fin R → ℕ) → Fin R → ℝ) (hx : ∀ m, IsWPFAllocation N m (x m)) :
    ∀ δ : ℝ, 0 < δ → ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε : ℝ, 0 < ε → ε < 1 → ε < ε₁ →
      ∀ π : State N → ℝ, IsStationary (rates N x ε) π →
        Summable (fun n => π n * wsum N n) ∧
        (((critical N).card : ℝ) * kappaMin N - δ) / ε ≤ ∑' n, π n * wsum N n ∧
        ∑' n, π n * wsum N n ≤ (((critical N).card : ℝ) * kappaMax N + δ) / ε := by sorry

end HTInsensBW.PhaseType
