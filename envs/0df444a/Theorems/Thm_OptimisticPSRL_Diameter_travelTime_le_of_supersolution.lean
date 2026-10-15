-- Prove2me | Theorems.Thm_OptimisticPSRL_Diameter_travelTime_le_of_supersolution
-- name    : OptimisticPSRL.Diameter.travelTime_le_of_supersolution
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T00:39:50.718983+00:00
-- url     : https://prove2.me/theorems/15b2db5c-7221-4435-b60d-9e9f736f7d0f
-- title:
--   Proof of Lemma 5.6, p. 13, (17) — 1 + Q†E ≤ E + δ1 implies E ≥ (1 − δ)Ẽ for the expected travel times Ẽ
-- statement:
--   Let $\mathcal M'$ be a finite MDP (in the application, the extended MDP $\tilde{\mathcal M}$) with transition probability vectors $Q_{s,a}$, let $\tilde\pi$ be a deterministic stationary policy, $s_2$ a target state, $\delta\in[0,1)$, and $E=(E_s)_{s\in\mathcal S}$ a vector with entries in $[0,\infty]$. Write $Q^{\dagger}_{\tilde\pi}$ for the $(S-1)\times(S-1)$ matrix with entries $Q_{s,\tilde\pi(s)}(s')$, $s,s'\neq s_2$. Suppose that for every $s\neq s_2$
--   $$1+\sum_{s'\neq s_2} Q_{s,\tilde\pi(s)}(s')\,E_{s'} \;\le\; E_s+\delta,$$
--   that is, $\mathbf 1+Q^{\dagger}_{\tilde\pi}E\le E+\delta\mathbf 1$ (equivalently $(I-Q^{\dagger}_{\tilde\pi})E\ge(1-\delta)\mathbf 1$, display (17)). Then the expected numbers of steps $\tilde E_s=T^{\tilde\pi}_{s\to s_2}$ to reach $s_2$ in $\mathcal M'$ under $\tilde\pi$ satisfy
--   $$(1-\delta)\,\tilde E_s \;\le\; E_s\qquad\text{for every } s\neq s_2.$$
--
--   This is the comparison step of the proof of Lemma 5.6: with $E$ the vector of minimum expected times of the true MDP and $\tilde\pi$ the policy that, in each state, picks a sample satisfying (16), it gives $E\ge(1-\delta)\tilde E$, hence $\tilde E_{s_1}\le D/(1-\delta)$.
--
--   **Formalization Note.** States are `Fin S` (0-based) and $\tilde E_s$ is the platform's `mdpTravelTime M' g s s₂`. The hypothesis is the left half of (17), $E\ge \mathbf 1+Q^{\dagger}_{\tilde\pi}E-\delta\mathbf 1$, with $\delta$ moved to the other side because $[0,\infty]$ has no subtraction; the conclusion is $E\ge(1-\delta)\tilde E$ without the matrix inverse $(I-Q^{\dagger}_{\tilde\pi})^{-1}$. Unlike the paper's argument, the statement does not assume that the entries of $Q$ are strictly positive (the paper derives this from the Dirichlet law of the samples); the transition vectors are arbitrary. Values may be $\infty$; sums and products are in $[0,\infty]$, and $1-\delta$ is computed in $\mathbb R_{\ge0}$ (positive since $\delta<1$).
-- source:
--   Agrawal & Jia, Posterior sampling for reinforcement learning: worst-case regret bounds, arXiv:1705.07041v3, p. 13, proof of Lemma 5.6, display (17) and the following display (E ≥ (1 − δ)Ẽ)

import Mathlib
import Definitions.Def_FiniteMDPLearning
open BanditAlgorithm NNReal ENNReal

namespace OptimisticPSRL.Diameter
theorem travelTime_le_of_supersolution {S A' : ℕ} (M' : FiniteMDP S A') (g : Fin S → Fin A')
    (tgt : Fin S) (E : Fin S → ℝ≥0∞) (δ : ℝ≥0) (hδ : δ < 1)
    (hsuper : ∀ s, s ≠ tgt →
      1 + ∑ s' ∈ Finset.univ.erase tgt, (M'.P s (g s) s' : ℝ≥0∞) * E s' ≤ E s + δ) :
    ∀ s, s ≠ tgt → ((1 - δ : ℝ≥0) : ℝ≥0∞) * mdpTravelTime M' g s tgt ≤ E s := by sorry
end OptimisticPSRL.Diameter
