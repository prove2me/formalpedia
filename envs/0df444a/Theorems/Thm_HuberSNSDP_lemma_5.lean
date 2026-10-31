-- Prove2me | Theorems.Thm_HuberSNSDP_lemma_5
-- name    : HuberSNSDP.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:23:22.897776+00:00
-- url     : https://prove2.me/theorems/3b9e2912-476e-48e3-b611-965e09ac5dbd
-- title:
--   Lemma 5 — $\langle H-V(0,H),V(0,H)\rangle\ge0$ for $V\in\partial\Phi(0,W)$
-- statement:
--   Let $W\in\mathbb S^n$. For every $V\in\partial\Phi(0,W)$,
--   $$\langle H-V(0,H),\,V(0,H)\rangle\ge0\qquad\text{for all }H\in\mathbb S^n.$$
--
--   This inequality, the analogue of the firm nonexpansiveness of $\partial\Pi_{\mathbb S^n_+}$, enters the proof of Proposition 2.
--
--   Differences from the source:
--   - encoding: $\mathbb S^n$, $\mathbb R^m$, $\mathbb X=\mathbb S^n\times\mathbb R^m\times\mathbb S^n$ with the trace inner product and Euclidean norms → `SymMat (Fin n)` (Frobenius inner product = trace inner product), `EuclideanSpace ℝ (Fin m)`, `WithLp 2` products; reason: Lean convention; the same spaces, inner products and norms
--   - encoding: "Let $W\in\mathbb S^n$ have the spectral decomposition (7)" → any $W$; reason: every symmetric matrix has a spectral decomposition, so the hypothesis excludes nothing
-- source:
--   Liang, Sun & Toh, A Squared Smoothing Newton Method for Semidefinite Programming, arXiv:2303.05825v4, Lemma 5, p.11

import Mathlib
import Definitions.Def_HuberSNSDP_Setting

open scoped RealInnerProductSpace Topology
open Filter SunNLSDP.Equiv NonsmoothNewton.Shared

namespace HuberSNSDP

/-- Lemma 5, p.11 (Liang, Sun & Toh, arXiv:2303.05825v4): for any `W ∈ Sⁿ` and any
`V ∈ ∂Φ(0, W)`, `⟨H − V(0, H), V(0, H)⟩ ≥ 0` for all `H ∈ Sⁿ`.

**Formalization Note.** The page's hypothesis "`W` has the spectral decomposition (7)" holds for
every `W` and is omitted. -/
theorem lemma_5 {n : ℕ} (W : SymMat (Fin n))
    (V : RS (Fin n) →L[ℝ] SymMat (Fin n)) (hV : V ∈ clarkeJac (PhiPair (ι := Fin n)) (rsPt 0 W))
    (H : SymMat (Fin n)) :
    0 ≤ ⟪H - V (rsPt 0 H), V (rsPt 0 H)⟫ := by sorry

end HuberSNSDP
