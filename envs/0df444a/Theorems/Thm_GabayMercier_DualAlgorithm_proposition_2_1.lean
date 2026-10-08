-- Prove2me | Theorems.Thm_GabayMercier_DualAlgorithm_proposition_2_1
-- name    : GabayMercier.DualAlgorithm.proposition_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T09:57:30.365394+00:00
-- url     : https://prove2.me/theorems/e7c93835-06e8-49ec-b8c7-a609b55e8754
-- title:
--   Proposition 2.1 — under (2.3), (2.5), (𝒫) has a unique solution
-- statement:
--   Let $V,Y$ be real Hilbert spaces, $A:V\to Y$ continuous linear, $b\in V'$, and $f=f_1+f_2$ with $f_1:Y\to\mathbb R$ convex, continuously differentiable with strongly monotone gradient (2.3), and $f_2:Y\to(-\infty,+\infty]$ proper, convex and lower semicontinuous. Assume (2.5): $|Av|^2\ge\alpha^2\|v\|^2$ for some $\alpha>0$. Assume also that $f_2(Av_0)<+\infty$ for some $v_0\in V$. Then the problem
--   $$(\mathcal P)\qquad \inf_{v\in V}\ \bigl\{f(Av)-\langle b,v\rangle\bigr\}$$
--   has exactly one solution $v^*$: $f(Av^*)-\langle b,v^*\rangle$ is finite and is at most $f(Av)-\langle b,v\rangle$ for every $v\in V$.
--
--   Existence and uniqueness of $v^*$ is what makes "the" solution in Theorem 3.1 meaningful; it also shows that the hypothesis "$v^*$ is a solution" of the goal theorem can be met.
--
--   **Formalization Note.** The paper states "under (2.3), (2.5)"; its proof also uses that $f_2$ is proper, convex and lower semicontinuous (the standing hypothesis (2.2)) and that $f_2\circ A$ is not identically $+\infty$ ("otherwise (𝒫) has no meaning", p. 9). Both are stated: the first through `StandingHyp`, which collects (2.2), (2.3), (2.5), the second as the hypothesis `hdom`. The qualification (2.4) is not assumed, as in the paper ("even if (2.4) is not satisfied").
-- source:
--   Gabay & Mercier, IRIA RR-126 (1975), hal-04716124v1, p. 9, Proposition 2.1

import Mathlib
import Definitions.Def_InertialFB_IFB_ConvexAnalysis
import Definitions.Def_GabayMercier_DualAlgorithm_Model

open Filter Topology InertialFB.IFB

namespace GabayMercier.DualAlgorithm

variable {V Y : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

/-- Proposition 2.1, p. 9: under (2.3), (2.5) (with `f₂` proper, convex, l.s.c., and `f₂ ∘ A`
not identically `+∞`, as the proof requires), (𝒫) has a unique solution. -/
theorem proposition_2_1 (A : V →L[ℝ] Y) (f₁ : Y → ℝ) (f₁' : Y → Y) (f₂ : Y → EReal)
    (b : StrongDual ℝ V) (γ α : ℝ) (h : StandingHyp A f₁ f₁' f₂ γ α)
    (hdom : ∃ v₀ : V, f₂ (A v₀) ≠ ⊤) :
    ∃! v : V, IsSolution A f₁ f₂ b v := by sorry

end GabayMercier.DualAlgorithm
