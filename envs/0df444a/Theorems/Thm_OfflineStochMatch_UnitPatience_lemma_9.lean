-- Prove2me | Theorems.Thm_OfflineStochMatch_UnitPatience_lemma_9
-- name    : OfflineStochMatch.UnitPatience.lemma_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T10:12:40.307089+00:00
-- url     : https://prove2.me/theorems/2ebcf00e-99b3-44b7-8f59-7444d8572803
-- title:
--   Lemma 9, p. 18 — E[W(v)] ≥ (1 − 1/e)·OPT(v) for every v ∈ V₂
-- statement:
--   For $v\in V_2$ let $\mathsf{OPT}(v)=\sum_{e\in\delta(v)}w_ez_e$ with $z_e=p_ey_e$. For every vertex $v\in V_2$, the expected weight the algorithm matches at $v$ satisfies
--   $$\mathbb E[W(v)]\ \ge\ \Big(1-\frac1e\Big)\mathsf{OPT}(v).$$
--
--   Summing over $v\in V_2$ gives Theorem 2.
--
--   **Formalization Note** Hypotheses are the standing ones of §4: $w_e\ge 0$, $p_e\in[0,1]$, $y$ feasible for LP (3) (in particular $\sum_{e\in\delta(v)}z_e\le 1$), $\mu$ an admissible rounding, and $\mathrm{ord}(v)$ a decreasing-weight order of $\delta(v)$.
-- source:
--   Brubach, Grammel, Ma, MacRury, Srinivasan, Improved Guarantees for Offline Stochastic Matching via New Ordered Contention Resolution Schemes, arXiv:2106.06892v3, p. 18, Lemma 9 (OPT(v) defined just before it)

import Mathlib
import Definitions.Def_OfflineStochMatch_UnitPatience_Setting

namespace OfflineStochMatch.UnitPatience

open Finset

theorem lemma_9 {V₁ V₂ E : Type} [Fintype E] [DecidableEq V₁] [DecidableEq V₂] [DecidableEq E]
    (G : BipGraph V₁ V₂ E) (w p y : E → ℝ) (t : V₂ → ℕ∞)
    (hw : ∀ e, 0 ≤ w e) (hp : ∀ e, 0 ≤ p e ∧ p e ≤ 1) (hy : LPFeasible G p y t)
    (μ : Finset E → ℝ) (hμ : IsRounding G y t μ)
    (ord : V₂ → List E) (hord : IsWeightOrder G w ord) (v : V₂) :
    (1 - Real.exp (-1)) * OPT G w p y v ≤ EW w p ord v μ := by sorry

end OfflineStochMatch.UnitPatience
