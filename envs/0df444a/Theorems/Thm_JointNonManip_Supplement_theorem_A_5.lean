-- Prove2me | Theorems.Thm_JointNonManip_Supplement_theorem_A_5
-- name    : JointNonManip.Supplement.theorem_A_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:30:49.105366+00:00
-- url     : https://prove2.me/theorems/e1d8bc0c-90e3-4cbe-b623-f7bd64800033
-- title:
--   Theorem A.5 — the defection-robust profile $A^\star_{L,T}$: swap regret bound (7), joint non-manipulability (8)–(9), completed menu near $S_{\mathrm{NE}}$
-- statement:
--   Fix a finite game with nonempty action sets, learner utilities $u_i:A\to[-1,1]$ and $d_0=|A_0|\ge2$, and use the parameters, codebook and error quantities of `JointNonManip.Supplement.Codebook`. For every horizon $T\ge1$, every admissible public codebook and every rule for computing auxiliary-game equilibria, the profile $A^\star_{L,T}$ has the following properties.
--
--   1. **No swap regret.** For every learner $i$ following the protocol, whatever the optimizer and the other learners do (admissibly),
--   $$\mathbb E[R_i^{\mathrm{sw}}(T)]\le B_i(T)+4\ell\gamma_TT+2h_i(T)+4\sqrt{2T\Lambda_T}+2+F_i(T)+\frac{4\alpha_TT}3,\tag{7}$$
--   with the maximum over swaps inside the expectation. The right-hand side is $o(T)$, and $\mathbb E[R_i^{\mathrm{sw}}(T)]\le B_i(T)+O_G(T^{3/4}\sqrt{\log T})$.
--   2. **Joint non-manipulability.** If all learners follow the protocol, then for every $u_0$ with $\|u_0\|_\infty\le1$, with $V=\max_{s\in S_{\mathrm{NE}}}\langle u_0,s\rangle$,
--   $$\sup_{\pi\in\Pi_T}\langle u_0,\phi_T(\pi,A^\star_{L,T})\rangle\le V+a_T+e_T,\tag{8}$$
--   $$\sup_{y\in\Delta(A_0)}\langle u_0,\phi_T(y^{\otimes T},A^\star_{L,T})\rangle\ge V-b_T-e_T.\tag{9}$$
--   Consequently the dynamic-versus-static payoff gap is at most $a_T+b_T+2e_T=a_T+b_T+4\ell\gamma_T+4\alpha_T/3=o(1)$.
--   3. **The completed menu.** If all learners follow the protocol, $\mathcal M^\star_T=\overline{\{\phi_T(\pi,A^\star_{L,T}):\pi\in\Pi_T\}}$ satisfies
--   $$d_{H,1}(\mathcal M^\star_T,S_{\mathrm{NE}})\le\max\{a_T+e_T,\,b_T+e_T\}=o(1).$$
--
--   All bounds are uniform over the policies indicated. The $o(1)$ statements hold for every family of admissible codebooks of polylogarithmic size $J_T\le K(\log(T+2))^\kappa$ (the paper's $J_T=(\log T)^{O_G(1)}$), and such codebooks, as well as auxiliary-equilibrium rules, exist.
--
--   The theorem unifies Theorem 3.3 with explicit rates: it adds robustness of each learner's swap-regret guarantee to deviations of the other learners and explicit non-asymptotic bounds for joint non-manipulability and the menu.
--
--   **Formalization Note** The suprema over policies are stated for every policy; the supremum over $\Delta(A_0)$ in (9), which is attained (the expected CSP is polynomial in $y$), is stated with an explicit $y$. $O_G(\cdot)$ is "there are $K$ and $T_0$ such that for all $T\ge T_0$"; $o(\cdot)$ is a limit as $T\to\infty$.
--
--   Differences from the source:
--   - encoding: a known horizon T → T ≥ 1 in every finite-horizon clause; reason: the horizon is a positive number of rounds t = 1, …, T, and the parameters (T^{−1/4}, division by T) are undefined at T = 0
--   - reading: "All common choices and tie-breaking rules are deterministic and fixed in advance" (net, c⋆, θ_j, z_j, reading profile, auxiliary equilibrium) → every bound is stated for every admissible codebook (Codebook u T) and every auxiliary-equilibrium selector; reason: the paper fixes them arbitrarily, so its bounds must hold for each choice
--   - reading: o(1) claims for "the fixed game", whose codebook has J_T = (log T)^{O_G(1)} → the o(1) claims for every family of admissible codebooks with J_T ≤ K (log(T + 2))^κ; reason: the paper's size claim is a property of its net, and with an arbitrarily large net ξ_T need not tend to 0
--   - reading: "Other players may adapt to the past and current mixed strategies, but must choose their current actions without observing an adhering learner's fresh action sample" → an adversary choosing a joint distribution of (c, a₋ᵢ) as a function of the whole realized past, independent of learner i's sample; reason: the largest class the sentence allows (learner i's current mixed strategy is a function of that past)
--   - reading: "for the finitely many smaller horizons, omit menu completion and monitor a fresh approachability run" → for m_T ≥ T the public state is a fresh approachability run from round 1 with monitoring, and the bounds are claimed with the same a_T, b_T for any codebook; reason: literal rule; the theorem's bounds are claimed for every horizon
--   - encoding: sup_{π∈Π_T} ≤ and sup_{y∈∆(A₀)} ≥ → ∀ π, ≤ and ∃ y, ≥; reason: the supremum over the compact ∆(A₀) of a polynomial function of y is attained
--   - encoding: O_G(T^{3/4}√log T) and o(·) → ∃ K, ∃ T₀, ∀ T ≥ T₀ and Filter.Tendsto … atTop (nhds 0); reason: Lean conventions
--   - encoding: V = max_{s∈S_NE}⟨u₀, s⟩, closure, d_{H,1} → real sSup of the image of S_NE, closure in ℝ^A, Metric.hausdorffEDist on PiLp 1 compared with ENNReal.ofReal; reason: S_NE is nonempty and compact and both sets are bounded, so these are the source's values
--   - encoding: the stationary distribution x = xQ and "for k_i = 1 the only action is played" → classical choice of a lottery with x = xQ, applied for every k_i; reason: Q has positive entries, so the stationary lottery is unique, and for k_i = 1 it is the point mass on the only action
--   - generalization: the theorem states the bounds; p.33 asserts "These choices are possible" → added conjuncts: admissible codebooks of polylogarithmic size exist for every T, and auxiliary-equilibrium selectors exist; reason: they make the universally quantified bounds non-vacuous; dropping them gives the source's statement
-- source:
--   Collina, Fullerton, Liu & Weinberg, Non-manipulability and Approachability Beyond Two-Player Games (manuscript, STOC 2027 submission), Theorem A.5, pp.35–36 (displays (7), (8), (9)); model, parameters and codebook, p.33; protocol, pp.33–34; bandit fallback and error quantities, p.35

import Mathlib
import Definitions.Def_JointNonManip_Supplement_UnifiedProtocol

namespace JointNonManip.Supplement

variable {A0 : Type} [Fintype A0] [DecidableEq A0]
variable {L : Type} [Fintype L] [DecidableEq L]
variable {Act : L → Type} [∀ i, Fintype (Act i)] [∀ i, DecidableEq (Act i)]

/-- **Theorem A.5: the unified defection-robust profile `A⋆_{L,T}`** (Collina, Fullerton, Liu &
Weinberg, *Non-manipulability and Approachability Beyond Two-Player Games*, manuscript (STOC 2027
submission), Theorem A.5, pp.35–36; the model, parameters, codebook and protocol on pp.33–35).

Fix a finite game with nonempty action sets, learner utilities in `[−1, 1]` and `d₀ = |A₀| ≥ 2`.
For every horizon `T ≥ 1`, every admissible public codebook `C` and every auxiliary-equilibrium
selector `S`, the profile `A⋆_{L,T}` satisfies:
1. **No swap regret.** For every learner `i` following the protocol and every admissible
   behaviour of the optimizer and the other learners, the expected realized swap regret (maximum
   over swaps inside the expectation) is at most
   `Bᵢ(T) + 4ℓγ_T T + 2hᵢ(T) + 4√(2TΛ_T) + 2 + Fᵢ(T) + 4α_T T/3` (7); this bound is `o(T)`, and
   in particular `E[R_i^sw(T)] ≤ Bᵢ(T) + O_G(T^{3/4}√(log T))`.
2. **Joint non-manipulability.** If all learners follow the protocol, then for every `u₀` with
   `‖u₀‖_∞ ≤ 1` and `V = max_{s ∈ S_NE} ⟨u₀, s⟩`: every policy `π ∈ Π_T` has
   `⟨u₀, φ_T(π, A⋆_{L,T})⟩ ≤ V + a_T + e_T` (8); some static `y^{⊗T}` has
   `⟨u₀, φ_T(y^{⊗T}, A⋆_{L,T})⟩ ≥ V − b_T − e_T` (9); hence the dynamic-versus-static gap is at
   most `a_T + b_T + 2e_T = a_T + b_T + 4ℓγ_T + 4α_T/3`.
3. **The completed menu.** `d_{H,1}(M⋆_T, S_NE) ≤ max{a_T + e_T, b_T + e_T}`.

The `o(1)` claims hold for every family of admissible codebooks of size
`J_T ≤ K (log(T + 2))^κ` ("For the fixed game, `J_T = (log T)^{O_G(1)}`", p.33), such families
exist, and auxiliary-equilibrium selectors exist ("These choices are possible", p.33).

**Formalization Note** Suprema over the policy class are stated pointwise (`∀ π`); the supremum
over the compact set `∆(A₀)` in (9) is attained (the expected CSP is polynomial in `y`), so it is
stated with `∃ y`. `O_G(·)` is `∃ K, ∃ T₀, ∀ T ≥ T₀`. `d_{H,1}` is the extended ℓ₁ Hausdorff
distance, compared with `ENNReal.ofReal`. -/
theorem theorem_A_5 [Nonempty A0] [∀ i, Nonempty (Act i)]
    (u : L → A0 × ((i : L) → Act i) → ℝ) (hu : ∀ i a, |u i a| ≤ 1)
    (hA0 : 2 ≤ Fintype.card A0) :
    -- Clause 1, bound (7)
    (∀ T : ℕ, 1 ≤ T → ∀ (C : Codebook u T) (S : AuxNESelector u) (i : L)
        (adv : Adversary A0 Act i T),
        advExpSwapRegret u S C i adv ≤ regretBound7 u i T) ∧
    -- Clause 1, `(7) = o(T)`
    (∀ i : L, Filter.Tendsto (fun T : ℕ => regretBound7 u i T / T) Filter.atTop (nhds 0)) ∧
    -- Clause 1, `E[R_i^sw(T)] ≤ Bᵢ(T) + O_G(T^{3/4} √(log T))`
    (∀ i : L, ∃ K : ℝ, ∃ T0 : ℕ, ∀ T : ℕ, T0 ≤ T → 1 ≤ T →
        ∀ (C : Codebook u T) (S : AuxNESelector u) (adv : Adversary A0 Act i T),
        advExpSwapRegret u S C i adv ≤
          BiT u i T + K * ((T : ℝ) ^ ((3 : ℝ) / 4) * Real.sqrt (Real.log T))) ∧
    -- Clause 2, (8), (9), the gap and its identity
    (∀ u0 : A0 × ((i : L) → Act i) → ℝ, (∀ a, |u0 a| ≤ 1) →
      ∀ T : ℕ, 1 ≤ T → ∀ (C : Codebook u T) (S : AuxNESelector u),
        (∀ π : Policy A0 Act T,
          pairing u0 (starExpCSP u S C π) ≤ valueV u u0 + aT C + eT L T) ∧
        (∃ (y : A0 → ℝ) (hy : AGT.IsLottery y),
          valueV u u0 - bT C - eT L T ≤ pairing u0 (starExpCSP u S C (Policy.static y hy T))) ∧
        (∀ π : Policy A0 Act T, ∃ (y : A0 → ℝ) (hy : AGT.IsLottery y),
          pairing u0 (starExpCSP u S C π) ≤
            pairing u0 (starExpCSP u S C (Policy.static y hy T)) + (aT C + bT C + 2 * eT L T)) ∧
        aT C + bT C + 2 * eT L T =
          aT C + bT C + 4 * (Fintype.card L : ℝ) * gammaT T + 4 * alphaT T / 3) ∧
    -- Clause 3, the completed menu
    (∀ T : ℕ, 1 ≤ T → ∀ (C : Codebook u T) (S : AuxNESelector u),
        hausdorffL1 (starMenu u S C) (SNE u) ≤
          ENNReal.ofReal (max (aT C + eT L T) (bT C + eT L T))) ∧
    -- The `o(1)` claims of clauses 2 and 3, for codebooks of polylogarithmic size
    (∀ (K : ℝ) (κ : ℕ) (C : ∀ T : ℕ, Codebook u T),
        (∀ T : ℕ, ((C T).J : ℝ) ≤ K * Real.log ((T : ℝ) + 2) ^ κ) →
        Filter.Tendsto (fun T => aT (C T) + bT (C T) + 2 * eT L T) Filter.atTop (nhds 0) ∧
        Filter.Tendsto (fun T => max (aT (C T) + eT L T) (bT (C T) + eT L T))
          Filter.atTop (nhds 0)) ∧
    -- These choices are possible
    (∃ (K : ℝ) (κ : ℕ), ∀ T : ℕ, ∃ C : Codebook u T,
        (C.J : ℝ) ≤ K * Real.log ((T : ℝ) + 2) ^ κ) ∧
    Nonempty (AuxNESelector u) := by sorry

end JointNonManip.Supplement
