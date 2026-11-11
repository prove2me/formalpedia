-- Prove2me | Theorems.Thm_LogConcaveLattice_Lift_theorem_1_1
-- name    : LogConcaveLattice.Lift.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:02:10.930819+00:00
-- url     : https://prove2.me/theorems/53280e4d-fc96-40b0-ab6b-1e28f4c6298f
-- title:
--   Theorem 1.1 — existence of the $(2\pi/e)$-strongly log-concave lattice lift, and its converse
-- statement:
--   **Existence.** Let $\Lambda\subseteq\mathbb R^n$ be a full-rank lattice such that its dual $\Lambda^*$ is weakly stable, i.e. $\det\Gamma\ge1$ for every sublattice $\Gamma\subseteq\Lambda^*$. Then there is a symmetric random vector $X\in\mathbb R^n$ with a smooth, strictly positive density $f:\mathbb R^n\to(0,\infty)$ such that
--   1. $f$ is $\alpha$-strongly log-concave with $\alpha=2\pi/e$: $\nabla^2(-\log f)(x)\succcurlyeq\frac{2\pi}{e}\,\mathrm{Id}$ for every $x$;
--   2. $X+\Lambda$ is uniform on $\mathbb R^n/\Lambda$, i.e.
--   $$\sum_{\lambda\in\Lambda}f(x+\lambda)=\frac1{\det\Lambda}\qquad\text{for all }x\in\mathbb R^n .$$
--   Symmetry means $f(-x)=f(x)$, and $f$ is a probability density: $f$ is integrable with $\int_{\mathbb R^n}f=1$.
--
--   **Converse.** Let $\alpha>0$ and let $\Lambda\subseteq\mathbb R^n$ be a full-rank lattice. If some smooth, strictly positive, even probability density $f$ is $\alpha$-strongly log-concave and satisfies $\sum_{\lambda\in\Lambda}f(x+\lambda)=1/\det\Lambda$ for all $x$, then the dilated dual lattice $\sqrt{2\pi/\alpha}\cdot\Lambda^*$ is weakly stable.
--
--   Theorem 1.1 thus characterizes, up to a universal dilation, the lattices with weakly stable dual by the existence of a strongly log-concave probability measure whose image modulo the lattice is uniform (the **log-concave lattice lift**). Through Hargé's theorem, the Bakry–Émery criterion and Milman's theorem it yields the covering-radius, flatness, log-Sobolev and reverse Minkowski consequences of the paper.
--
--   Differences from the source:
--   - generalization: the converse for "such a density f", i.e. with α = 2π/e → the converse for every α > 0, with the scale √(2π/α); reason: the proof on p. 15 is written for a density with arbitrary curvature α > 0, and α = 2π/e is the instance stated in the theorem
--   - encoding: symmetric random vector X with smooth, strictly positive density f → f(−x) = f(x) for all x, f integrable with ∫ f = 1, smoothness and positivity as part of the strong log-concavity predicate (as in its definition on p. 3); reason: for a continuous density, symmetry of the law is evenness of f; same instances
--   - encoding: Σ_{λ∈Λ} f(x + λ) = 1/det Λ → HasSum (λ ↦ f(x + λ)) (1/ZLattice.covolume Λ) for every x; det Γ of a sublattice → the Gram determinant of a lattice basis (1 for Γ = {0}); reason: the source's own "i.e." form of uniformity, with the sum required to converge; the determinant computed in the span; same instances
-- source:
--   Letwin, Reis, Rothvoss, Strongly Log-Concave Measures and Lattices, STOC 2027 submission #401 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/401.pdf, Theorem 1.1, p. 3 (weak stability p. 2; strong log-concavity p. 3; proof pp. 14–15)

import Mathlib
import Definitions.Def_LogConcaveLattice_Lift_Lattice
import Definitions.Def_LogConcaveLattice_Lift_StronglyLogConcave

open MeasureTheory

namespace LogConcaveLattice.Lift

/-- **Theorem 1.1** (Letwin–Reis–Rothvoss, p. 3). Existence: for every full-rank lattice
`Λ ⊆ ℝⁿ` whose dual is weakly stable there is a smooth, strictly positive, even probability
density `f` that is `(2π/e)`-strongly log-concave and satisfies `∑_{λ∈Λ} f(x+λ) = 1/det Λ` for
every `x`. Converse (stated, as in its proof on p. 15, for every curvature `α > 0`): if such a
density exists with `α` in place of `2π/e`, then `√(2π/α) · Λ*` is weakly stable. -/
theorem theorem_1_1 :
    (∀ (n : ℕ) (Λ : Submodule ℤ (V n)) [DiscreteTopology Λ] [IsZLattice ℝ Λ],
      WeaklyStable (dual Λ) →
      ∃ f : V n → ℝ,
        IsStronglyLogConcave (2 * Real.pi / Real.exp 1) f ∧
        (∀ x, f (-x) = f x) ∧
        Integrable f ∧ ∫ x, f x = 1 ∧
        ∀ x : V n, HasSum (fun l : Λ => f (x + l)) (1 / ZLattice.covolume Λ)) ∧
    (∀ α : ℝ, 0 < α →
      ∀ (n : ℕ) (Λ : Submodule ℤ (V n)) [DiscreteTopology Λ] [IsZLattice ℝ Λ] (f : V n → ℝ),
        IsStronglyLogConcave α f →
        (∀ x, f (-x) = f x) →
        Integrable f → ∫ x, f x = 1 →
        (∀ x : V n, HasSum (fun l : Λ => f (x + l)) (1 / ZLattice.covolume Λ)) →
        WeaklyStable (scaleLattice (Real.sqrt (2 * Real.pi / α)) (dual Λ))) := by sorry

end LogConcaveLattice.Lift
