-- Prove2me | Theorems.Thm_MifflinSemismooth_Extremal_limsup_le_dirDeriv
-- name    : MifflinSemismooth.Extremal.limsup_le_dirDeriv
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:37:24.444973+00:00
-- url     : https://prove2.me/theorems/1a3f3b8a-1a22-4ebd-8520-8d33922d095c
-- title:
--   Proof of Theorem 2, p. 8 — lim sup ⟨g_k,d⟩ ≤ E′(x;d) for g_k ∈ ∂E(x + t_k d + θ_k)
-- statement:
--   Assume the hypotheses of Theorem 2 with $E$ of the max form: $B\subseteq\mathbb R^n$ open, $U\subseteq T$ sequentially compact, $f$ continuous on $B\times U$, $E(x)=\max\{f(x,u):u\in U\}$ on $B$, $f(\cdot,u)$ differentiable on $B$ for each $u\in U$, and $\nabla_x f$ continuous and bounded on $B\times U$. Let $x\in B$, $d\in\mathbb R^n$, and let $t_k>0$, $\theta_k\in\mathbb R^n$ with $t_k\to 0$ and $\theta_k/t_k\to 0$. Let $g_k\in\partial E(x_k)$, where $x_k=x+t_kd+\theta_k$. Then
--
--   $$\limsup_{k\to\infty}\langle g_k,d\rangle\le E'(x;d).$$
--
--   This is the first half of the proof that $E$ is semismooth: the upper bound on the possible slopes $\langle g_k,d\rangle$. The remainder of the proof shows the matching lower bound.
--
--   **Formalization Note.** The statement asserts that $E'(x;d)$ exists, with some value $L$, and that for every $\varepsilon>0$ eventually $\langle g_k,d\rangle\le L+\varepsilon$. This is exactly $\limsup_k\langle g_k,d\rangle\le E'(x;d)$ in the extended reals, written without Lean's default value of `limsup` on unbounded sequences.
-- source:
--   Mifflin, Semismooth and semiconvex functions in constrained optimization, IIASA Research Report RR-76-21 (December 1976), p. 8, §3, proof of Theorem 2, display after "From Theorem 1 and Proposition 1"

import Mathlib
import Definitions.Def_ClarkeGradients_Shared_genDirDeriv
import Definitions.Def_MifflinSemismooth_Extremal_Basic
import Definitions.Def_MifflinSemismooth_Extremal_Setting

open Filter Topology

namespace MifflinSemismooth.Extremal

/-- Mifflin (1976), proof of Theorem 2, p. 8: for the max form, with `x_k = x + t_k d + θ_k`,
`t_k ↓ 0`, `θ_k / t_k → 0` and `g_k ∈ ∂E(x_k)`, `E'(x; d)` exists and
`lim sup_k ⟨g_k, d⟩ ≤ E'(x; d)`, stated as: for every `ε > 0`, eventually
`⟨g_k, d⟩ ≤ E'(x; d) + ε`. -/
theorem limsup_le_dirDeriv {n : ℕ} {T : Type*} [TopologicalSpace T]
    (B : Set (EuclideanSpace ℝ (Fin n))) (U : Set T) (f : EuclideanSpace ℝ (Fin n) → T → ℝ)
    (E : EuclideanSpace ℝ (Fin n) → ℝ) (hB : IsOpen B) (hU : IsSeqCompact U)
    (ha : HypA B U f) (hd : HypD B U f E)
    (hdiff : ∀ u ∈ U, ∀ x ∈ B, DifferentiableAt ℝ (fun y => f y u) x)
    (hcont : ContinuousOn
      (fun p : EuclideanSpace ℝ (Fin n) × T => gradient (fun y => f y p.2) p.1) (B ×ˢ U))
    (hbdd : ∃ M : ℝ, ∀ x ∈ B, ∀ u ∈ U, ‖gradient (fun y => f y u) x‖ ≤ M)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ B) (d : EuclideanSpace ℝ (Fin n))
    (t : ℕ → ℝ) (θ g : ℕ → EuclideanSpace ℝ (Fin n))
    (ht : ∀ k, 0 < t k) (ht0 : Tendsto t atTop (𝓝 0))
    (hθ : Tendsto (fun k => (t k)⁻¹ • θ k) atTop (𝓝 0))
    (hg : ∀ k, g k ∈ genGrad E (x + t k • d + θ k)) :
    ∃ L : ℝ, HasDirDeriv E x d L ∧
      ∀ ε > 0, ∀ᶠ k in atTop, inner ℝ (g k) d ≤ L + ε := by sorry

end MifflinSemismooth.Extremal
