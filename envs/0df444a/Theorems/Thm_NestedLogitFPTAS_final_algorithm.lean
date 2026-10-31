-- Prove2me | Theorems.Thm_NestedLogitFPTAS_final_algorithm
-- name    : NestedLogitFPTAS.final_algorithm
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:28:38.704029+00:00
-- url     : https://prove2.me/theorems/6476bd44-72ea-4e7c-922b-20669153c2a2
-- title:
--   "Final algorithm", p.14 (corrected: grids $\mathcal D_\omega$, $\mathcal D_\rho$) — the output traces the best $\mathcal C$-feasible pair
-- statement:
--   Let $\epsilon>0$. Call $(\omega,\rho)\in\mathcal D_\omega\times\mathcal D_\rho$ $\mathcal C$-feasible when $\tilde F(1,\omega,\rho)\le\mathcal C$. The program returns an assortment if and only if some pair is $\mathcal C$-feasible. In that case it selects a $\mathcal C$-feasible pair $(\tilde\omega,\tilde\rho)$ maximizing $\rho/(w_0+\omega)$ over the $\mathcal C$-feasible pairs, and its output $\tilde S$ satisfies:
--
--   1. $\tilde F(1,\tilde\omega,\tilde\rho)=c(\tilde S)$, so $\tilde S$ is $\mathcal C$-feasible;
--   2. there is a path of states from $(1,\tilde\omega,\tilde\rho)$ to $(M+1,0,0)$, with choices $\tilde\omega_k,\tilde\rho_k$ at each nest attaining (4), such that $\tilde S_k$ is the set computed by $\mathcal A(k,\tilde\omega_k,\tilde\rho_k)$.
--
--   This is the description of the output that the proof of Lemma 3.3 expands in §3.6.
--
--   **Formalization Note** The path is given by grid indices.
--
--   Differences from the source:
--   - encoding: products in pairwise-disjoint nests N₁, …, N_M; assortments S = (S₁, …, S_M); non-negative γₘ → Fin n with nest : Fin n → Fin M; S : Finset (Fin n) with Sₘ = part S m; 0 < M, nonempty nests, 0 < γₘ; reason: same instances wherever the paper is defined: at γₘ = 0 the ratio γ⁺/γ⁻ and the power ωₖ^{1/γₖ} are undefined, and W↓, r_min, π_min minimize over Nₘ
--   - generalization: signs of c, C, w₀ are not stated; w₀ read as a positive weight → c and C real of any sign, w₀ ≥ 0, w₀ₘ ≥ 0; R(∅) = 0 at w₀ = 0; reason: the proofs use no sign of c or C, and every instance with nonnegative costs and positive w₀ is covered
--   - encoding: any ϵ > 0 in the parameters ξω, ξρ, δω, δρ → the program uses ϵ̂ = min(ϵ, 1) in all its parameters; reason: no change for ϵ ≤ 1; the parameters need ϵ ≤ 80 and for ϵ ≥ 1 the guarantee is empty
--   - correction: Dω with p ≤ γ⁺·log_{1+ξω}(W↑/W↓); Dρ from π_min r_min W↓^{γ⁺} with q ≤ γ⁺·log_{1+ξρ}((r_max/(π_min r_min))(W↑/W↓)) → Pω = ⌈(γ⁺ log(W↑/W↓) + log M)/log(1+ξω)⌉ + M + 1; Lρ = (1−ξρ)^M π_min r_min W↓^{γ⁺}; Qρ = ⌈log(M r_max W↑^{γ⁺}/Lρ)/log(1+ξρ)⌉; reason: the printed tops cover one nest but the states hold sums: M = 2, one product per nest, r = w = c = 1, γ = 1, w₀ₘ = 0, w₀ = 2, C = 2 gives Dω = Dρ = {0, 1}, so R(S̃) ≤ 1/3 < (1−ϵ)/2 for ϵ < 1/3; and the printed bottom rounds (1−ξρ)·1 down to 0 there, so A(1, ω*₁, 0) = ∞ > c(S₁)
--   - correction: G over all subsets S ⊆ {1, …, t}; the search may return ∅ → the search reads G over nonempty subsets (an extra table); the recursion starts at t = 0; reason: one product with w = 0.05, r = 12, c = 1, w₀ₖ = 1, γₖ = 1, ωₖ = ρₖ = 1, δρ = 1/2, δω = 1/16: the neighbourhood is nonempty, but (η, ζ) = (0, 0) has G = 0, and ∅ is outside N_(2δω,20δρ)
-- source:
--   Segev, Approximation Schemes for Capacity-Constrained Assortment Optimization under the Nested Logit Model, SSRN #3553264 (Mar 2020), §3.4, "Final algorithm", p.14; §3.6, p.15

import Mathlib
import Definitions.Def_NestedLogitFPTAS_Model
import Definitions.Def_NestedLogitFPTAS_Grids
import Definitions.Def_NestedLogitFPTAS_SingleNest
import Definitions.Def_NestedLogitFPTAS_Program

namespace NestedLogitFPTAS

/-- Segev, SSRN #3553264 (Mar 2020), "Final algorithm", §3.4, p.14, and the expansion of (4) in §3.6,
p.15: the program returns an assortment exactly when some pair `(ω, ρ) ∈ Dω × Dρ` is `C`-feasible,
that is, `F̃(1, ω, ρ) ≤ C`. Its selected pair maximizes `ρ/(w₀ + ω)` over the `C`-feasible pairs, and
the assortment `S̃` is the one corresponding to `(1, ω̃, ρ̃)`: there is a path of states attaining (4)
at each nest, ending at `(M+1, 0, 0)`, along which `S̃ₖ` is the assortment computed by `A`. Its total
cost is `F̃(1, ω̃, ρ̃)`, so `S̃` is `C`-feasible.

**Formalization Note.** `pState k`, `qState k` index the state at the paper's nest `k + 1`, and
`pNest k`, `qNest k` the paper's choice of `ω̃ₖ₊₁`, `ρ̃ₖ₊₁`. At `w₀ + ω = 0` the ratio is Lean's `0`. -/
theorem final_algorithm {n M : ℕ} (I : Instance n M) (hI : I.Standing) {ε : ℝ} (hε : 0 < ε) :
    ((∃ S', I.output ε = some S') ↔
      ∃ p q, p < I.Pomega ε + 2 ∧ q < I.Qrho ε + 2 ∧ I.Ftilde ε 0 p q ≤ ((I.C : ℝ) : WithTop ℝ)) ∧
    ∀ S', I.output ε = some S' →
      ∃ p q, I.selected ε = some (p, q) ∧ p < I.Pomega ε + 2 ∧ q < I.Qrho ε + 2 ∧
        I.Ftilde ε 0 p q ≤ ((I.C : ℝ) : WithTop ℝ) ∧
        (∀ p' q', p' < I.Pomega ε + 2 → q' < I.Qrho ε + 2 →
          I.Ftilde ε 0 p' q' ≤ ((I.C : ℝ) : WithTop ℝ) →
          I.rhoAt ε q' / (I.w0 + I.omegaAt ε p') ≤ I.rhoAt ε q / (I.w0 + I.omegaAt ε p)) ∧
        I.Ftilde ε 0 p q = ((I.cost S' : ℝ) : WithTop ℝ) ∧
        ∃ pState qState pNest qNest : ℕ → ℕ,
          pState 0 = p ∧ qState 0 = q ∧ pState M = 0 ∧ qState M = 0 ∧
          ∀ k : Fin M,
            pState k < I.Pomega ε + 2 ∧ qState k < I.Qrho ε + 2 ∧
            pNest k < I.Pomega ε + 2 ∧ qNest k < I.Qrho ε + 2 ∧
            I.omegaAt ε (pNest k) + I.omegaAt ε (pState (k.val + 1)) ≤ I.omegaAt ε (pState k) ∧
            I.rhoAt ε (qState k) ≤ I.rhoAt ε (qNest k) + I.rhoAt ε (qState (k.val + 1)) ∧
            I.Ftilde ε k (pState k) (qState k) =
              I.Acost (I.deltaOmega ε) (I.deltaRho ε) k
                  (I.omegaAt ε (pNest k)) (I.rhoAt ε (qNest k)) +
                I.Ftilde ε (k.val + 1) (pState (k.val + 1)) (qState (k.val + 1)) ∧
            I.Aset (I.deltaOmega ε) (I.deltaRho ε) k
                (I.omegaAt ε (pNest k)) (I.rhoAt ε (qNest k)) = some (I.part S' k) := by sorry

end NestedLogitFPTAS
