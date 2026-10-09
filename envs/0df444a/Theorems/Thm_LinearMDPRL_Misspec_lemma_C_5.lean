-- Prove2me | Theorems.Thm_LinearMDPRL_Misspec_lemma_C_5
-- name    : LinearMDPRL.Misspec.lemma_C_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T02:36:15.894919+00:00
-- url     : https://prove2.me/theorems/8b6dfcaf-6ce1-432d-b9bb-d72d8113cd14
-- title:
--   Lemma C.5, p. 22 — on 𝔈, ⟨φ, w^k_h⟩ − Q^π_h = P_h(V^k_{h+1} − V^π_{h+1}) + Δ with |Δ| ≤ β_k‖φ‖_{(Λ^k_h)^{-1}} + 4Hζ
-- statement:
--   For every value $C\ge0$ of the constant in the event $\mathfrak E$ of Lemma C.3 there is an absolute threshold $c_{\beta,0}>0$ such that the following holds for every $c_\beta\ge c_{\beta,0}$. Let the MDP be $\zeta$-approximately linear with $d,H,K\ge1$, let $p\in(0,1)$, $\iota=\log(2dT/p)$, $\beta_k=c_\beta(d\sqrt\iota+\zeta\sqrt{kd})H$, and let $w^k_h,V^k_h,\Lambda^k_h$ be computed by Algorithm 1 with $\lambda=1$ from data on which $\mathfrak E$ holds. Then for every measurable policy $\pi$ and all $(x,a,h,k)\in\mathcal S\times\mathcal A\times[H]\times[K]$,
--   $$\langle\phi(x,a),w^k_h\rangle-Q^\pi_h(x,a)=\mathbb P_h(V^k_{h+1}-V^\pi_{h+1})(x,a)+\Delta^k_h(x,a)$$
--   for some $\Delta^k_h(x,a)$ with
--   $$|\Delta^k_h(x,a)|\le\beta_k\sqrt{\phi(x,a)^\top(\Lambda^k_h)^{-1}\phi(x,a)}+4H\zeta.$$
--
--   This is the key estimate of the misspecified analysis: the least-squares value estimate tracks the Bellman backup of any policy up to the exploration bonus and a misspecification error linear in $\zeta$.
--
--   **Formalization Note** "For some $\Delta$ with $|\Delta|\le b$" is stated as $|\langle\phi,w^k_h\rangle-Q^\pi_h-\mathbb P_h(V^k_{h+1}-V^\pi_{h+1})|\le b$. The page fixes $C$ to Lemma C.3's constant; stating the lemma for every $C\ge0$, with the threshold $c_{\beta,0}$ depending on $C$ only, includes that case. The page asks for one absolute $c_\beta$; its proof (p. 24) needs only $c_\beta\ge2$ and $c'\sqrt{\log2+\log(c_\beta+1)}\le c_\beta\sqrt{\log2}$, which holds for every $c_\beta$ beyond a threshold, so the threshold form is what the proof gives and lets Lemmas C.5–C.7 be used with one common $c_\beta$. The data are arbitrary apart from $\mathfrak E$. The proof uses $\sup|V^k_{h+1}|\le H$, which Algorithm 1 does not enforce from below (see Lemma C.3); the statement is formalized as printed.
-- source:
--   arXiv:1907.05388v2, Lemma C.5, p. 22 (proof pp. 22–24)

import Mathlib
import Definitions.Def_LinearMDPRL_Linear_Model
import Definitions.Def_LinearMDPRL_Linear_LSVIUCB
import Definitions.Def_LinearMDPRL_Misspec_ApproxLinearMDP
import Definitions.Def_LinearMDPRL_Misspec_Event

open MeasureTheory ProbabilityTheory Matrix

namespace LinearMDPRL.Misspec

universe u v w

/-- **Lemma C.5** (p. 22). For every value `C ≥ 0` of the constant of the event `𝔈` there is an
absolute threshold `c_β₀ > 0` such that for every `c_β ≥ c_β₀`, with `λ = 1`, `β_k = c_β (d√ι + ζ√(kd)) H`, on the event
`𝔈`, for every measurable policy `π` and all `(x, a, h, k) ∈ S × A × [H] × [K]`,
`⟨φ(x, a), w^k_h⟩ − LinearMDPRL.Linear.Q^π_h(x, a) = P_h(LinearMDPRL.Linear.V^k_{h+1} − LinearMDPRL.Linear.V^π_{h+1})(x, a) + Δ^k_h(x, a)` with
`|Δ^k_h(x, a)| ≤ β_k √(φ(x, a)^⊤ (Λ^k_h)^{-1} φ(x, a)) + 4Hζ`. -/
theorem lemma_C_5 :
    ∀ C : ℝ, 0 ≤ C → ∃ cβ₀ : ℝ, 0 < cβ₀ ∧ ∀ cβ : ℝ, cβ₀ ≤ cβ →
    ∀ {S : Type u} {A : Type v} [MeasurableSpace S] [Fintype A] [Nonempty A] [LinearOrder A]
      [MeasurableSpace A] [DiscreteMeasurableSpace A] (d H K : ℕ), 1 ≤ d → 1 ≤ H → 1 ≤ K →
    ∀ (M : LinearMDPRL.Linear.EpisodicMDP S A) (φ : S → A → EuclideanSpace ℝ (Fin d)) (ζ : ℝ),
      IsApproxLinearMDP M H d φ ζ →
    ∀ p : ℝ, 0 < p → p < 1 →
    ∀ (xs : ℕ → ℕ → S) (as : ℕ → ℕ → A), goodEvent M φ ζ C cβ p H K xs as →
    ∀ π : LinearMDPRL.Linear.Policy S A, LinearMDPRL.Linear.IsMeasurablePolicy π →
    ∀ k ∈ Finset.Icc 1 K, ∀ h ∈ Finset.Icc 1 H, ∀ (x : S) (a : A),
      |inner ℝ (φ x a) (LinearMDPRL.Linear.lsviW φ M.r 1 (betaMis cβ ζ d H K p) H xs as k h) - LinearMDPRL.Linear.Q M H π h x a
          - ∫ y, (LinearMDPRL.Linear.lsviV φ M.r 1 (betaMis cβ ζ d H K p) H xs as k (h + 1) y - LinearMDPRL.Linear.V M H π (h + 1) y)
              ∂(M.P h (x, a))|
        ≤ betaMis cβ ζ d H K p k *
            Real.sqrt (WithLp.ofLp (φ x a) ⬝ᵥ (LinearMDPRL.Linear.gram φ 1 xs as k h)⁻¹ *ᵥ WithLp.ofLp (φ x a))
          + 4 * H * ζ := by sorry

end LinearMDPRL.Misspec
