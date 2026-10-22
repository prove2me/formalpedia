-- Prove2me | Theorems.Thm_OptimisticPSRL_Diameter_first_step_travelTime
-- name    : OptimisticPSRL.Diameter.first_step_travelTime
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T00:39:51.593148+00:00
-- url     : https://prove2.me/theorems/93b63822-f57f-42f2-b70f-5257a3262e66
-- title:
--   Proof of Lemma 5.6, p. 13 — first-step analysis: E = 1 + P†_π E for expected travel times
-- statement:
--   Let $\mathcal M$ be a finite MDP with transition probability vectors $P_{s,a}$, let $\pi:\mathcal S\to\mathcal A$ be a deterministic stationary policy, and let $T^{\pi}_{s\to s_2}$ denote the expected number of steps to reach the target $s_2$ from $s$ under $\pi$. For every state $s\neq s_2$,
--   $$T^{\pi}_{s\to s_2} \;=\; 1+\sum_{s'\neq s_2} P_{s,\pi(s)}(s')\,T^{\pi}_{s'\to s_2}.$$
--
--   In matrix form, the vector $E=(T^{\pi}_{s\to s_2})_{s\neq s_2}$ solves $E=\mathbf 1+P^{\dagger}_{\pi}E$, where $P^{\dagger}_{\pi}$ is the $(S-1)\times(S-1)$ matrix with entries $P_{s,\pi(s)}(s')$, $s,s'\neq s_2$. This is the first-step equation the proof of Lemma 5.6 starts from.
--
--   **Formalization Note.** States and actions are 0-based (`Fin S`, `Fin A`); $T^{\pi}_{s\to s_2}$ is the platform's `mdpTravelTime M f s s₂` in $[0,\infty]$. The identity is stated for every deterministic stationary policy (the proof uses it for one) and with no finiteness assumption: both sides may equal $\infty$. Products and sums are taken in $[0,\infty]$, where $0\cdot\infty=0$.
-- source:
--   Agrawal & Jia, Posterior sampling for reinforcement learning: worst-case regret bounds, arXiv:1705.07041v3, p. 13, proof of Lemma 5.6, first display (E = 1 + P†_π E)

import Mathlib
import Definitions.Def_FiniteMDPLearning
open BanditAlgorithm NNReal ENNReal

namespace OptimisticPSRL.Diameter
theorem first_step_travelTime {S A : ℕ} (M : FiniteMDP S A) (f : Fin S → Fin A)
    (src tgt : Fin S) (hne : src ≠ tgt) :
    mdpTravelTime M f src tgt =
      1 + ∑ s' ∈ Finset.univ.erase tgt, (M.P src (f src) s' : ℝ≥0∞) * mdpTravelTime M f s' tgt := by sorry
end OptimisticPSRL.Diameter
