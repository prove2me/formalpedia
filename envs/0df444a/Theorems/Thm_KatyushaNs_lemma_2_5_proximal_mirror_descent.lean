-- Prove2me | Theorems.Thm_KatyushaNs_lemma_2_5_proximal_mirror_descent
-- name    : KatyushaNs.lemma_2_5_proximal_mirror_descent
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:50:24.580406+00:00
-- url     : https://prove2.me/theorems/10f617ae-cf24-425a-925c-2313d00ea076
-- title:
--   Lemma 2.5: proximal mirror descent
-- statement:
--   Let $\psi$ be $\sigma$-strongly convex ($\sigma \ge 0$) with effective domain $D$, let $\alpha > 0$, and fix a vector $\widetilde\nabla_{k+1}$ and a point $z_k$. Let
--   $$z_{k+1} = \operatorname*{arg\,min}_z \Big\{ \frac12\|z - z_k\|^2 + \alpha\langle \widetilde\nabla_{k+1}, z - z_k\rangle + \alpha\psi(z) - \alpha\psi(z_k) \Big\}.$$
--   Then for every $u \in D$,
--   $$\alpha\langle \widetilde\nabla_{k+1}, z_{k+1} - u\rangle + \alpha\psi(z_{k+1}) - \alpha\psi(u) \le -\frac12\|z_k - z_{k+1}\|^2 + \frac12\|z_k - u\|^2 - \frac{1 + \alpha\sigma}{2}\|z_{k+1} - u\|^2.$$
--
--   This is the one-step inequality of proximal mirror descent; it is deterministic (the estimator is fixed).
--
--   Differences from the source:
--   - generalization: ψ convex and lower semicontinuous (Problem (1.1), p. 1) → ψ convex on its effective domain, no lower semicontinuity; reason: lower semicontinuity only guarantees that the arg mins exist; their existence is part of the hypotheses (the prox predicates / the run). Every lsc convex ψ is covered, so the statement specializes to the paper's
--   - encoding: ψ : ℝᵈ → ℝ ∪ {+∞} → a set D (dom ψ) and real values ψ : ℝᵈ → ℝ with ConvexOn ℝ D ψ (or StrongConvexOn), F = f + ψ on D; reason: every convex extended-valued ψ is of this form and conversely; same instances
--   - encoding: ψ σ-SC (Definition 1.2, subgradient form) → StrongConvexOn D σ ψ with σ ≥ 0 (Jensen form, modulus σ/2·r²); reason: for convex functions the two forms agree; σ = 0 is plain convexity
--   - reading: step size α (sign unstated) → α > 0; reason: α is the step size, α_s = 1/(3τ_{1,s}L) > 0 in Algorithms 1 and 2; the arg min of line 11 needs 1/α > 0
--   - encoding: for all u ∈ ℝᵈ → for all u ∈ D; reason: for u ∉ D the paper's ψ(u) = +∞ makes the left side −∞; no content is lost
--   - encoding: arg min of ½‖z − z_k‖² + α⟨∇̃, z − z_k⟩ + αψ(z) − αψ(z_k) → IsQuadProxMin D ψ α⁻¹ z_k ∇̃ z_{k+1}, the arg min of (1/(2α))‖z − z_k‖² + ⟨∇̃, z⟩ + ψ(z); reason: the paper's objective is α times this one plus a constant; same minimizer for α > 0
-- source:
--   Allen-Zhu, Katyusha: The First Direct Acceleration of Stochastic Gradient Methods, arXiv:1603.05953v6, Lemma 2.5, p. 9

import Mathlib
import Definitions.Def_KatyushaNs_IsQuadProxMin

namespace KatyushaNs

/-- **Lemma 2.5 (proximal mirror descent).**
Allen-Zhu, *Katyusha: The First Direct Acceleration of Stochastic Gradient Methods*,
arXiv:1603.05953v6, Lemma 2.5, p. 9 (PDF p. 10): "Suppose ψ(·) is σ-SC. Then, fixing ∇̃_{k+1}
and letting z_{k+1} = arg min_z { 1/2 ‖z − z_k‖² + α⟨∇̃_{k+1}, z − z_k⟩ + αψ(z) − αψ(z_k) },
it satisfies for all u ∈ Rd,
α⟨∇̃_{k+1}, z_{k+1} − u⟩ + αψ(z_{k+1}) − αψ(u) ≤ −1/2 ‖z_k − z_{k+1}‖² + 1/2 ‖z_k − u‖²
− (1 + ασ)/2 ‖z_{k+1} − u‖²."

Setting: `ψ` is `σ`-strongly convex on its effective domain `D` (`σ ≥ 0`), `α > 0`, `g` is a
fixed vector (the estimator `∇̃_{k+1}`), and `zplus ∈ D` minimizes
`z ↦ (1/(2α))‖z − zk‖² + ⟨g, z⟩ + ψ(z)`. Conclusion: for every `u ∈ D`,
`α⟨g, zplus − u⟩ + αψ(zplus) − αψ(u) ≤ −½‖zk − zplus‖² + ½‖zk − u‖² − (1 + ασ)/2 ‖zplus − u‖²`.

**Formalization Note.** `σ`-SC is Mathlib's `StrongConvexOn D σ ψ` (modulus `σ/2·r²`, matching
Definition 1.2; `σ = 0` is convexity). The paper's arg min objective is `α` times the objective of
`IsQuadProxMin D ψ α⁻¹ zk g zplus` plus a constant, so the minimizer is the same. For `u ∉ D`
the paper's `ψ(u) = +∞` makes the left side `−∞`, so only `u ∈ D` carries content. -/
theorem lemma_2_5_proximal_mirror_descent {d : ℕ} {D : Set (EuclideanSpace ℝ (Fin d))}
    {ψ : EuclideanSpace ℝ (Fin d) → ℝ} {σ : ℝ} (hσ : 0 ≤ σ) (hψσ : StrongConvexOn D σ ψ)
    {α : ℝ} (hα : 0 < α) {g zk zplus : EuclideanSpace ℝ (Fin d)}
    (hz : IsQuadProxMin D ψ α⁻¹ zk g zplus) :
    ∀ u ∈ D, α * inner ℝ g (zplus - u) + α * ψ zplus - α * ψ u ≤
      -(1 / 2) * ‖zk - zplus‖ ^ 2 + 1 / 2 * ‖zk - u‖ ^ 2 -
        (1 + α * σ) / 2 * ‖zplus - u‖ ^ 2 := by sorry

end KatyushaNs
