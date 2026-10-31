-- Prove2me | Theorems.Thm_HuberSNSDP_lemma_9
-- name    : HuberSNSDP.lemma_9
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:23:21.814986+00:00
-- url     : https://prove2.me/theorems/8185c238-f6db-4640-9007-047e93e7a7d3
-- title:
--   Lemma 9 — $\langle\Delta X,\Delta Z\rangle\le\Gamma_{\bar X}(-\bar Z,\Delta X)$ when $\Delta X=\bar V(0,\Delta X-\Delta Z)$
-- statement:
--   Let $(\bar X,\bar y,\bar Z)$ be a KKT point of (1)–(2), $\bar W=\bar X-\bar Z$ and $\bar V\in\partial\Phi(0,\bar W)$. Then for all $\Delta X,\Delta Z\in\mathbb S^n$ with $\Delta X=\bar V(0,\Delta X-\Delta Z)$,
--   $$\langle\Delta X,\Delta Z\rangle\le\Gamma_{\bar X}(-\bar Z,\Delta X),$$
--   where $\Gamma_B(S,H)=2\langle S,HB^\dagger H\rangle$ (11) and $B^\dagger$ is the Moore–Penrose pseudoinverse.
--
--   This links $\partial\Phi(0,\cdot)$ to the curvature term of the strong second-order sufficient condition in the proof of Proposition 2.
--
--   Differences from the source:
--   - encoding: $\mathbb S^n$, $\mathbb R^m$, $\mathbb X=\mathbb S^n\times\mathbb R^m\times\mathbb S^n$ with the trace inner product and Euclidean norms → `SymMat (Fin n)` (Frobenius inner product = trace inner product), `EuclideanSpace ℝ (Fin m)`, `WithLp 2` products; reason: Lean convention; the same spaces, inner products and norms
--   - encoding: the standing assumption of p.2 (an optimal solution of (1) exists and Slater's condition holds), stated once for the whole paper → the explicit hypothesis `D.Standing`; reason: the paper assumes it throughout ("In this paper, we assume", p.2)
--   - encoding: $\Gamma_{\bar X}(-\bar Z,\Delta X)$ (11) → the published `upsilon X̄ (−Z̄) ΔX` $=2\,\mathrm{tr}((-\bar Z)^T\Delta X\bar X^\dagger\Delta X)$; reason: the same function
-- source:
--   Liang, Sun & Toh, A Squared Smoothing Newton Method for Semidefinite Programming, arXiv:2303.05825v4, Lemma 9, p.15

import Mathlib
import Definitions.Def_HuberSNSDP_Setting

open scoped RealInnerProductSpace Topology
open Filter SunNLSDP.Equiv NonsmoothNewton.Shared

namespace HuberSNSDP

/-- Lemma 9, p.15 (Liang, Sun & Toh, arXiv:2303.05825v4).

Let `(X̄, ȳ, Z̄)` be a KKT point, `W̄ := X̄ − Z̄` and `V̄ ∈ ∂Φ(0, W̄)`. Then for any `ΔX, ΔZ ∈ Sⁿ` with
`ΔX = V̄(0, ΔX − ΔZ)`, `⟨ΔX, ΔZ⟩ ≤ Γ_X̄(−Z̄, ΔX)`, where `Γ_B(S, H) = 2⟨S, HB†H⟩` (11).

**Formalization Note.** `Γ_X̄(−Z̄, ΔX)` is the published `upsilon X̄ (−Z̄) ΔX`; the standing
assumption of p.2 is a hypothesis. -/
theorem lemma_9 {n m : ℕ} (D : SDPData n m) (hD : D.Standing) (Xbar : SymMat (Fin n))
    (ybar : EuclideanSpace ℝ (Fin m)) (Zbar : SymMat (Fin n)) (hK : D.KKT Xbar ybar Zbar)
    (Vbar : RS (Fin n) →L[ℝ] SymMat (Fin n))
    (hV : Vbar ∈ clarkeJac (PhiPair (ι := Fin n)) (rsPt 0 (Xbar - Zbar)))
    (ΔX ΔZ : SymMat (Fin n)) (hΔ : ΔX = Vbar (rsPt 0 (ΔX - ΔZ))) :
    ⟪ΔX, ΔZ⟫ ≤ upsilon Xbar (-Zbar) ΔX := by sorry

end HuberSNSDP
