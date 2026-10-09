-- Prove2me | Theorems.Thm_LinearMDPRL_Linear_lemma_B_4
-- name    : LinearMDPRL.Linear.lemma_B_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T01:46:04.008046+00:00
-- url     : https://prove2.me/theorems/fdadcedf-f531-4ab1-bc0c-af776bbfb247
-- title:
--   Lemma B.4, p. 17 — on 𝔈, ⟨φ, w^k_h⟩ − Q^π_h = P_h(V^k_{h+1} − V^π_{h+1}) + Δ^k_h with |Δ^k_h| ≤ β‖φ‖_{(Λ^k_h)^{-1}}
-- statement:
--   Work under Assumption A with $d,H,K\ge1$ and $p\in(0,1)$, and let $C\ge0$ be the constant of the event $\mathfrak E$ of Lemma B.3. There is an absolute constant $c_\beta>0$ such that, for LSVI-UCB with $\lambda=1$ and $\beta=c_\beta\cdot dH\sqrt\iota$, $\iota=\log(2dT/p)$, and for any fixed measurable policy $\pi$, on the event $\mathfrak E$ we have for all $(x,a,h,k)\in\mathcal S\times\mathcal A\times[H]\times[K]$
--   $$
--   \langle\phi(x,a),w^k_h\rangle-Q^\pi_h(x,a)=\mathbb P_h(V^k_{h+1}-V^\pi_{h+1})(x,a)+\Delta^k_h(x,a)
--   $$
--   for some $\Delta^k_h(x,a)$ with
--   $$
--   |\Delta^k_h(x,a)|\le\beta\sqrt{\phi(x,a)^\top(\Lambda^k_h)^{-1}\phi(x,a)} .
--   $$
--
--   This is the key technical lemma of the analysis: the error of the estimated action-value function, measured against any policy, propagates backwards through the true transition up to a term controlled by the bonus.
--
--   **Formalization Note.** "For some $\Delta$ with $|\Delta|\le\cdots$" is stated as the absolute-value bound on the difference of the two sides. The order "for every $C$ there is $c_\beta$" is the paper's dependence: $c_\beta$ is chosen after the absolute constant of Lemma B.3. The statement uses the paper’s existential bonus constant. The event is evaluated on arbitrary data (the lemma is deterministic on $\mathfrak E$); the policy is assumed measurable. $\mathbb P_hf(x,a)=\int f\,d\mathbb P_h(\cdot\mid x,a)$.
-- source:
--   Jin, Yang, Wang, Jordan, arXiv:1907.05388v2, Lemma B.4, p. 17

import Mathlib
import Definitions.Def_LinearMDPRL_Linear_Model
import Definitions.Def_LinearMDPRL_Linear_LSVIUCB
import Definitions.Def_LinearMDPRL_Linear_LinearMDP
import Definitions.Def_LinearMDPRL_Linear_ProofObjects

namespace LinearMDPRL.Linear

open MeasureTheory ProbabilityTheory Matrix

/-- **Lemma B.4** (arXiv:1907.05388v2, p. 17). For the absolute constant `C` of the event `𝔈` of
Lemma B.3 there is an absolute constant `c_β > 0` such that, for `β = c_β · dH√ι`,
`ι = log(2dT/p)`, `λ = 1`, and any fixed (measurable) policy `π`, on the event `𝔈` we have for all
`(x, a, h, k) ∈ S × A × [H] × [K]`
`⟨φ(x, a), w^k_h⟩ − Q^π_h(x, a) = P_h(V^k_{h+1} − V^π_{h+1})(x, a) + Δ^k_h(x, a)` with
`|Δ^k_h(x, a)| ≤ β √(φ(x, a)^⊤ (Λ^k_h)^{-1} φ(x, a))`. -/
theorem lemma_B_4 :
    ∀ C : ℝ, 0 ≤ C → ∃ cβ : ℝ, 0 < cβ ∧
      ∀ {S A : Type} [MeasurableSpace S] [Fintype A] [Nonempty A] [LinearOrder A]
        [MeasurableSpace A] [DiscreteMeasurableSpace A] (d H K : ℕ), 1 ≤ d → 1 ≤ H → 1 ≤ K →
      ∀ (M : EpisodicMDP S A) (φ : S → A → EuclideanSpace ℝ (Fin d)), IsLinearMDP M H d φ →
      ∀ p : ℝ, 0 < p → p < 1 →
      ∀ (xs : ℕ → ℕ → S) (as : ℕ → ℕ → A), goodEvent M φ C cβ p H K xs as →
      ∀ π : Policy S A, IsMeasurablePolicy π →
      ∀ k ∈ Finset.Icc 1 K, ∀ h ∈ Finset.Icc 1 H, ∀ (x : S) (a : A),
        |inner ℝ (φ x a)
              (lsviW φ M.r 1 (fun _ => cβ * d * H * Real.sqrt (iota d K H p)) H xs as k h)
            - Q M H π h x a
            - ∫ y, (lsviV φ M.r 1 (fun _ => cβ * d * H * Real.sqrt (iota d K H p)) H xs as k
                  (h + 1) y - V M H π (h + 1) y) ∂(M.P h (x, a))|
          ≤ cβ * d * H * Real.sqrt (iota d K H p) *
              Real.sqrt (WithLp.ofLp (φ x a) ⬝ᵥ ((gram φ 1 xs as k h)⁻¹ *ᵥ WithLp.ofLp (φ x a)))
          := by sorry

end LinearMDPRL.Linear
