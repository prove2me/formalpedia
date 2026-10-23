-- Prove2me | Theorems.Thm_NonstatRL_PerStep_eq32_bias_bounded
-- name    : NonstatRL.PerStep.eq32_bias_bounded
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T06:18:25.762913+00:00
-- url     : https://prove2.me/theorems/db1296c2-2342-41b3-8bb5-6cd1f966723f
-- title:
--   (32) — optimistic bias is between zero and 2D
-- statement:
--   Consider an episode of the paper's nonstationary finite MDP algorithm. Each state has a nonempty finite allowed action set, $S>1$, $0<\delta<1$, and widening $\eta\ge0$. At the episode start, the local reward and transition estimation-error events hold. The EVI output satisfies its optimistic and near-optimality contract. A transition model with diameter at most $D$ has every allowed row in the widened episode-start transition confidence region. Then every component of the output bias obeys
--
--   $$0\le\tilde\gamma_{\tau(m)}(s)\le 2D\qquad(s\in\mathcal S).$$
--
--   This controls transition-value errors in the later lemmas. **Formalization Note** The events and confidence sets are evaluated at the episode start. The diameter uses extended nonnegative reals and includes state return times.
-- source:
--   Cheung, Simchi-Levi & Zhu, Non-Stationary Reinforcement Learning: The Blessing of (More) Optimism, arXiv:1906.02922v4, p. 39, display (32)

import Mathlib
import Definitions.Def_NonstatRL_PerStep_EVIOutput

open BanditAlgorithm ENNReal

namespace NonstatRL.PerStep

theorem eq32_bias_bounded {S A : ℕ} (hS : 1 < S)
    (M : ℕ → FiniteMDP S A) (As : Fin S → Finset (Fin A))
    (hAs : ∀ s, (As s).Nonempty) (T : ℕ)
    (δ : ℝ) (hδ : 0 < δ ∧ δ < 1) (η : ℝ) (hη : 0 ≤ η)
    (W : ℕ) (st : ℕ → Fin S) (ac : ℕ → Fin A) (R : ℕ → ℝ)
    (τm : ℕ) (hτ : τm < T)
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
    ∀ s : Fin S, 0 ≤ γt s ∧ γt s ≤ 2 * D := by sorry

end NonstatRL.PerStep
