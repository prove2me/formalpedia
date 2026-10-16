-- Prove2me | Theorems.Thm_NonstatRL_PerStep_lemma4_optimism_under_drift
-- name    : NonstatRL.PerStep.lemma4_optimism_under_drift
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T06:18:21.908989+00:00
-- url     : https://prove2.me/theorems/cd966874-fcc6-47b9-a0c9-2f13fb6776e7
-- title:
--   Lemma 4 — optimistic gain under drift
-- statement:
--   Consider an episode of the paper's nonstationary finite MDP algorithm. Each state has a nonempty finite allowed action set, $S>1$, $0<\delta<1$, and widening $\eta\ge0$. At the episode start, the local reward and transition estimation-error events hold. The EVI output satisfies its optimistic and near-optimality contract. A transition model with diameter at most $D$ has every allowed row in the widened episode-start transition confidence region. For every round $t$ at or after this episode start and before the horizon,
--
--   $$\tilde\rho_{\tau(m)}\ge\rho_t^*-\operatorname{var}_{r,t}-2D\operatorname{var}_{p,t}.$$
--
--   The result compares the optimistic episode-start gain with the current MDP's optimal long-run gain. **Formalization Note** The optimal gain is the allowed-action occupancy-LP value. The statement includes unvisited pairs; it has no positive-count assumption.
-- source:
--   Cheung, Simchi-Levi & Zhu, Non-Stationary Reinforcement Learning: The Blessing of (More) Optimism, arXiv:1906.02922v4, p. 38, Lemma 4

import Mathlib
import Definitions.Def_NonstatRL_PerStep_EVIOutput

open BanditAlgorithm ENNReal

namespace NonstatRL.PerStep

theorem lemma4_optimism_under_drift {S A : ℕ} (hS : 1 < S)
    (M : ℕ → FiniteMDP S A) (As : Fin S → Finset (Fin A))
    (hAs : ∀ s, (As s).Nonempty) (T : ℕ)
    (δ : ℝ) (hδ : 0 < δ ∧ δ < 1) (η : ℝ) (hη : 0 ≤ η)
    (W : ℕ) (st : ℕ → Fin S) (ac : ℕ → Fin A) (R : ℕ → ℝ)
    (τm t : ℕ) (ht : τm ≤ t ∧ t < T)
    (heR : EventR M As T δ st ac R (τm - W) τm)
    (heP : EventP M As T δ st ac (τm - W) τm)
    (πt : Fin S → Fin A) (rt : Fin S → Fin A → ℝ)
    (pt : Fin S → Fin A → Fin S → ℝ) (ρt : ℝ) (γt : Fin S → ℝ)
    (hevi : IsEVIOutput As T δ η W τm st ac R πt rt pt ρt γt)
    (D : ℝ) (Mw : FiniteMDP S A)
    (hw : ∀ s a, a ∈ As s →
      (fun s' => (Mw.P s a s' : ℝ)) ∈
        Hp As T δ st ac (τm - W) τm η s a)
    (hdiam : NonstatRL.Oracle.diameter Mw As ≤ ENNReal.ofReal D) :
    NonstatRL.Oracle.optGain (M t) As - varR M As (τm - W) t -
      2 * D * varP M As (τm - W) t ≤ ρt := by sorry

end NonstatRL.PerStep
