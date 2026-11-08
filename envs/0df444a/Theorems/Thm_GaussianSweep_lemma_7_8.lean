-- Prove2me | Theorems.Thm_GaussianSweep_lemma_7_8
-- name    : GaussianSweep.lemma_7_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:54:17.15884+00:00
-- url     : https://prove2.me/theorems/491bbf28-0954-462a-81b9-ae5ccd08bb40
-- title:
--   Lemma 7.8 — grid: frontiers between grid thresholds
-- statement:
--   Let $y$ be any labeling of a graph $G$, let $\tau_0 < \tau_1 < \dots < \tau_K$, and for $0 \le j < K$ let $N_j = |\{v : \tau_j < y_v \le \tau_{j+1}\}|$.
--
--   1. If $\tau_j \le \tau < \tau_{j+1}$, then $|\partial^+ S_\tau| \le |\partial^+ S_{\tau_{j+1}}| + N_j$ and $|\partial^- S_\tau| \le |\partial^- S_{\tau_j}| + N_j$.
--   2. If $\tau < \tau_0$, then $|\partial^+ S_\tau| \le \Delta(G)\cdot|\{v : y_v \le \tau_0\}|$ and $|\partial^- S_\tau| \le |\{v : y_v \le \tau_0\}|$.
--   3. If $\tau \ge \tau_K$, then $|\partial^+ S_\tau| \le |\{v : y_v > \tau_K\}|$.
--
--   This deterministic interpolation bounds the frontier at every threshold by frontiers at finitely many grid thresholds plus window counts.
--
--   **Formalization Note** The grid is a strictly increasing map $\tau : \{0, \dots, K\} \to \mathbb R$.
--
--   Differences from the source:
--   - encoding: τ₀ < τ₁ < ⋯ < τ_K → a strictly increasing τ : Fin (K + 1) → ℝ; reason: same grids
--   - encoding: a finite simple graph G → a SimpleGraph on a finite vertex type V (Fintype), n = card V; reason: every finite graph is isomorphic to one on a finite type; pathwidth and degrees are invariant
-- source:
--   Gaspers, Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Lemma 7.8, p.42 (PDF p.44)

import Mathlib
import Definitions.Def_GaussianSweep_outerFrontier
import Definitions.Def_GaussianSweep_innerFrontier

namespace GaussianSweep

/-- Lemma 7.8 (grid) (Gaspers, *Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms*, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Lemma 7.8, p.42 (PDF p.44)). Let `y` be any labeling of a graph `G`,
`τ₀ < τ₁ < ⋯ < τ_K`, and `N_j = |{v : τ_j < y_v ≤ τ_{j+1}}|` for `0 ≤ j < K`. (i) If
`τ_j ≤ τ < τ_{j+1}`, then `|∂⁺S_τ| ≤ |∂⁺S_{τ_{j+1}}| + N_j` and `|∂⁻S_τ| ≤ |∂⁻S_{τ_j}| + N_j`.
(ii) If `τ < τ₀`, then `|∂⁺S_τ| ≤ Δ(G)·|{v : y_v ≤ τ₀}|` and `|∂⁻S_τ| ≤ |{v : y_v ≤ τ₀}|`.
(iii) If `τ ≥ τ_K`, then `|∂⁺S_τ| ≤ |{v : y_v > τ_K}|`.

**Formalization Note** The grid is a strictly increasing `τ : Fin (K + 1) → ℝ`; for `j : Fin K`,
`τ_j` and `τ_{j+1}` are `τ j.castSucc` and `τ j.succ`. -/
theorem lemma_7_8 {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (y : V → ℝ)
    (K : ℕ) (τ : Fin (K + 1) → ℝ) (hτ : StrictMono τ) :
    (∀ (j : Fin K) (t : ℝ), τ j.castSucc ≤ t → t < τ j.succ →
      (outerFrontier G y t).card ≤ (outerFrontier G y (τ j.succ)).card +
          (Finset.univ.filter fun v => τ j.castSucc < y v ∧ y v ≤ τ j.succ).card ∧
      (innerFrontier G y t).card ≤ (innerFrontier G y (τ j.castSucc)).card +
          (Finset.univ.filter fun v => τ j.castSucc < y v ∧ y v ≤ τ j.succ).card) ∧
    (∀ t : ℝ, t < τ 0 →
      (outerFrontier G y t).card ≤ G.maxDegree * (Finset.univ.filter fun v => y v ≤ τ 0).card ∧
      (innerFrontier G y t).card ≤ (Finset.univ.filter fun v => y v ≤ τ 0).card) ∧
    (∀ t : ℝ, τ (Fin.last K) ≤ t →
      (outerFrontier G y t).card ≤ (Finset.univ.filter fun v => τ (Fin.last K) < y v).card) := by sorry

end GaussianSweep
