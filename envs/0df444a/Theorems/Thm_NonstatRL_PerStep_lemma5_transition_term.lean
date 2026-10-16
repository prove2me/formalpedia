-- Prove2me | Theorems.Thm_NonstatRL_PerStep_lemma5_transition_term
-- name    : NonstatRL.PerStep.lemma5_transition_term
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T06:18:15.049017+00:00
-- url     : https://prove2.me/theorems/51b2787d-f8a2-4b6e-b301-d16254690525
-- title:
--   Lemma 5 — transition contribution error
-- statement:
--   Consider an episode of the paper's nonstationary finite MDP algorithm. Each state has a nonempty finite allowed action set, $S>1$, $0<\delta<1$, and widening $\eta\ge0$. At the episode start, the local reward and transition estimation-error events hold. The EVI output satisfies its optimistic and near-optimality contract. A transition model with diameter at most $D$ has every allowed row in the widened episode-start transition confidence region. For every allowed state-action pair $(s,a)$ and round $t$ at or after the episode start and before the horizon,
--
--   $$
--   \left|\sum_{s'}\tilde p_{\tau(m)}(s'\mid s,a)\tilde\gamma_{\tau(m)}(s')-\sum_{s'}p_t(s'\mid s,a)\tilde\gamma_{\tau(m)}(s')\right|
--   \le 2D\bigl[\operatorname{var}_{p,t}+2\operatorname{rad}_{p,\tau(m)}(s,a)+\eta\bigr].
--   $$
--
--   This bounds the transition term used in the per-step regret inequality. **Formalization Note** The statement covers unvisited pairs. The radius is computed from the episode-start window and the actual number of allowed state-action pairs.
-- source:
--   Cheung, Simchi-Levi & Zhu, Non-Stationary Reinforcement Learning: The Blessing of (More) Optimism, arXiv:1906.02922v4, p. 38, Lemma 5

import Mathlib
import Definitions.Def_NonstatRL_PerStep_EVIOutput

open BanditAlgorithm ENNReal

namespace NonstatRL.PerStep

theorem lemma5_transition_term {S A : ℕ} (hS : 1 < S)
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
    (hdiam : NonstatRL.Oracle.diameter Mw As ≤ ENNReal.ofReal D)
    (s : Fin S) (a : Fin A) (ha : a ∈ As s) :
    |(∑ s' : Fin S, pt s a s' * γt s') -
      (∑ s' : Fin S, ((M t).P s a s' : ℝ) * γt s')| ≤
    2 * D * (varP M As (τm - W) t +
      2 * radP As T δ (countPlus st ac (τm - W) τm s a) + η) := by sorry

end NonstatRL.PerStep
