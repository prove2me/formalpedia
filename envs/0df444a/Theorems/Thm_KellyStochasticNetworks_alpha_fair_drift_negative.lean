-- Prove2me | Theorems.Thm_KellyStochasticNetworks_alpha_fair_drift_negative
-- name    : KellyStochasticNetworks.alpha_fair_drift_negative
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-18T16:52:41.240449+00:00
-- url     : https://prove2.me/theorems/1b04158d-8cd5-4f43-a68d-8420eb4ce998
-- title:
--   Theorem 8.2 — the Lyapunov drift is uniformly negative under the stability condition
-- statement:
--   Consider a network carrying flows on $R$ routes over $J$ resources, in which flows on route $r$
--   arrive at rate $\nu_r$, carry exponentially distributed files of parameter $\mu_r$, and are served
--   at the weighted $\alpha$-fair rates. Write $\rho_r = \nu_r/\mu_r$ for the **load** on route $r$,
--   and suppose the stability condition (8.2) holds:
--   $$\sum_{r : j \in r}\rho_r < C_j \qquad\text{for every resource } j .$$
--
--   Then there is an $\epsilon > 0$, depending only on the loads and the capacities, such that for
--   **every** vector $n$ of flow counts and the corresponding $\alpha$-fair aggregate rates $X = X(n)$,
--   $$
--   \sum_r w_r\,\rho_r^{-\alpha}\,n_r^{\alpha}\bigl(\rho_r - X_r\bigr)
--   \;\le\; -\epsilon\sum_r w_r\,n_r^{\alpha}\,\rho_r^{1-\alpha}.
--   $$
--
--   The left-hand side is the drift of the Lyapunov function
--   $L(n) = \sum_r (w_r/\mu_r)\rho_r^{-\alpha}n_r^{\alpha+1}/(\alpha+1)$, by the identity (8.3). The
--   inequality therefore says that the drift is not merely negative but bounded away from zero by a
--   fixed multiple of a function that grows with $n$ — which is what a Foster–Lyapunov criterion needs
--   to conclude that the flow-count process is positive recurrent, and hence that the network is
--   stable.
--
--   The uniformity of $\epsilon$ in $n$ is the substance, and it comes from the shape of the
--   objective: $n$ enters only through the common factor $n_r^{\alpha}$ on both sides. The negativity
--   itself comes from a single application of concavity at a well-chosen point. Since (8.2) is a
--   *strict* inequality, the inflated load vector $(1+\epsilon)\rho$ is still feasible for the
--   $\alpha$-fair problem, so the tangent-plane inequality (8.5) applies to it; dividing through by
--   $(1+\epsilon)^{\alpha}$ produces exactly the displayed bound.
--
--   **Formalization Note** This is the deterministic half of Theorem 8.2. The theorem itself asserts
--   positive recurrence of a continuous-time Markov process on a countable state space, established by
--   a Foster–Lyapunov criterion whose remaining hypotheses the book leaves to Exercises 8.6 and D.2,
--   and there is no theory of such processes in Lean's mathematical library to state it against. What
--   is formalized here is the drift inequality the proof turns on, exactly as the book displays it,
--   including the $\epsilon$; the probabilistic wrapper and the necessity half, which is a coupling
--   argument, are quoted rather than formalized.
--
--   The $\alpha$-fair allocation is identified by its maximizing property rather than constructed, and
--   the feasible set is the one published in mission VII of this series.
-- source:
--   Kelly & Yudovina, Stochastic Networks, CUP 2014, pp. 189-191 (PDF pp. 197-199), Theorem 8.2 and its proof: 'Theorem 8.2 The Markov process n is positive recurrent (i.e. has an equilibrium distribution) if and only if sum_{r : j in r} rho_r < C_j for all j in J. (8.2)' The proof bounds the drift (8.3) using the concavity inequality (8.5) and concludes '(1/delta t) E[L(n(t+delta t)) - L(n(t)) | n(t)] <= -epsilon sum_r w_r n_r^alpha rho_r^{-alpha+1}.' sha256 ec271d555059aee58613e5e9a98b8346214b16185c527314f5d94c1ac8b17b6a

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_KellyStochasticNetworks_Congestion
import Definitions.Def_KellyStochasticNetworks_FlowLevel

namespace KellyStochasticNetworks

theorem alpha_fair_drift_negative {J R : ℕ} (A : Fin J → Fin R → ℝ) (C : Fin J → ℝ)
    (w ρ : Fin R → ℝ) (α : ℝ) (hα : 0 < α)
    (hA : ∀ j r, A j r = 0 ∨ A j r = 1) (hw : ∀ r, 0 < w r) (hρ : ∀ r, 0 < ρ r)
    (hstab : ∀ j, linkFlow A ρ j < C j) :
    ∃ ε > 0, ∀ n : Fin R → ℝ, (∀ r, 0 < n r) →
      ∀ X : Fin R → ℝ, (∀ r, 0 < X r) → X ∈ networkFeasible A C →
        IsMaxOn (alphaFairObjective w n α) (networkFeasible A C ∩ {Y | ∀ r, 0 < Y r}) X →
        (∑ r, w r * ρ r ^ (-α) * n r ^ α * (ρ r - X r))
          ≤ -ε * ∑ r, w r * n r ^ α * ρ r ^ (1 - α) := by sorry

end KellyStochasticNetworks
