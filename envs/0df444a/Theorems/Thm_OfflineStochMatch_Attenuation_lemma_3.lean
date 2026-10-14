-- Prove2me | Theorems.Thm_OfflineStochMatch_Attenuation_lemma_3
-- name    : OfflineStochMatch.Attenuation.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:29:57.326876+00:00
-- url     : https://prove2.me/theorems/1ad36ce5-bfc4-4a16-8412-0174076c0468
-- title:
--   Lemma 3, p. 11 — ∏_{f∈E₁(r)}(1 − x a(f) y_f) ≥ e^{−x Σ_{f∈E₁(r)} y_f} for an effective attenuation
-- statement:
--   Let $G = (V,E)$ be a finite graph with activeness probabilities $p_f \in [0,1]$ and values $y_f \in [0,1]$, and let $\tilde a$ be an effective attenuation function (Definition 3), with $a(f) = \tilde a(p_f y_f)$. Fix an edge $e$, one of its endpoints $r$, and $x \in [0,1]$. Let
--   $$E_1(r) = \{ f \in \delta(r) \setminus \{e\} : p_f = 1 \}.$$
--   Then
--   $$\prod_{f \in E_1(r)} \bigl(1 - x\, a(f)\, y_f\bigr) \;\ge\; \exp\Bigl(-x \sum_{f \in E_1(r)} y_f\Bigr).$$
--
--   In the proof of Theorem 1, $x$ is the arrival time of $e$, and the left side is the conditional probability that no edge of $E_1(r)$ arriving before $e$ is probed; the lemma bounds it by the value obtained in the limit of many small edges.
--
--   **Formalization Note** The arrival time $x$ ranges over the closed interval $[0,1]$, as in the integral (8) that the lemma feeds.
-- source:
--   Brubach, Grammel, Ma, MacRury, Srinivasan, Improved Guarantees for Offline Stochastic Matching via New Ordered Contention Resolution Schemes, arXiv:2106.06892v3, p. 11, Lemma 3 (with the definition of E(r), E_b(r) on p. 11)

import Mathlib
import Definitions.Def_OfflineStochMatch_Attenuation_Setting

namespace OfflineStochMatch.Attenuation

theorem lemma_3 {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E) (p y : E → ℝ) (aT : ℝ → ℝ)
    (haT : IsEffective aT) (hp : ∀ f, 0 ≤ p f ∧ p f ≤ 1) (hy : ∀ f, 0 ≤ y f ∧ y f ≤ 1)
    (e : E) (r : V) (hr : r ∈ G.ends e) (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    Real.exp (-(x * ∑ f ∈ (incident G r).filter (fun f => f ≠ e ∧ p f = 1), y f))
      ≤ ∏ f ∈ (incident G r).filter (fun f => f ≠ e ∧ p f = 1),
          (1 - x * attProb aT p y f * y f) := by sorry

end OfflineStochMatch.Attenuation
