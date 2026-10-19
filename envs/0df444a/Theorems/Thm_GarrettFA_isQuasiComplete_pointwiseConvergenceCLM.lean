-- Prove2me | Theorems.Thm_GarrettFA_isQuasiComplete_pointwiseConvergenceCLM
-- name    : GarrettFA.isQuasiComplete_pointwiseConvergenceCLM
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-12T19:43:35.950334+00:00
-- url     : https://prove2.me/theorems/25f84e7a-08d5-4b22-af1f-a92a02a56a26
-- title:
--   Thm. 4.1.1 — quasi-completeness of $\mathrm{Hom}^o(X,Y)$ with the pointwise topology
-- statement:
--   Let $X$ be a Fréchet space or an LF-space and let $Y$ be a Hausdorff, locally convex, quasi-complete topological vector space, both over $\mathbb K=\mathbb R$ or $\mathbb C$. Let $\mathrm{Hom}^o(X,Y)$ be the space of continuous linear maps $X\to Y$ with the topology given by the seminorms
--
--   $$p_{x,U}(T)=\inf\{\,t>0 : Tx\in tU\,\}\qquad(x\in X,\ U \text{ a convex balanced neighbourhood of } 0 \text{ in } Y).$$
--
--   Then
--
--   $$\mathrm{Hom}^o(X,Y)\ \text{ is quasi-complete.}$$
--
--   For Hilbert spaces $X,Y$ this topology is the strong operator topology; replacing $Y$ by its weak topology gives the weak operator topology.
--
--   **Formalization Note** $\mathrm{Hom}^o(X,Y)$ is Mathlib's space `X →Lₚₜ[𝕜] Y` of continuous linear maps with the topology of pointwise convergence. Since $Y$ is locally convex, convex balanced neighbourhoods form a basis at $0$, so this is the $p_{x,U}$-topology. $Y$ is assumed locally convex and Hausdorff, the standing conventions of the notes; the notes' proof uses both.
-- source:
--   Paul Garrett, *Completeness and quasi-completeness* (lecture notes, April 24, 2014), http://www.math.umn.edu/~garrett/m/fun/notes_2012-13/07d_quasi-completeness.pdf, p. 6, Theorem 4.1.1 (with the topology of §4.1)

import Definitions.Def_GarrettFA_IsQuasiComplete
import Definitions.Def_GarrettFA_IsFrechetSpace
import Definitions.Def_GarrettFA_IsLFSpace
open scoped PointwiseConvergenceCLM

namespace GarrettFA
theorem isQuasiComplete_pointwiseConvergenceCLM {𝕜 : Type*} [RCLike 𝕜] {X : Type*} [AddCommGroup X] [Module 𝕜 X] [Module ℝ X]
    [IsScalarTower ℝ 𝕜 X] [UniformSpace X] [IsUniformAddGroup X] [ContinuousSMul 𝕜 X] [T2Space X]
    (hX : IsFrechetSpace 𝕜 X ∨ IsLFSpace 𝕜 X)
    {Y : Type*} [AddCommGroup Y] [Module 𝕜 Y] [Module ℝ Y] [IsScalarTower ℝ 𝕜 Y]
    [TopologicalSpace Y] [IsTopologicalAddGroup Y] [ContinuousSMul 𝕜 Y] [LocallyConvexSpace ℝ Y]
    [T2Space Y]
    (hY : IsQuasiComplete 𝕜 Y) :
    IsQuasiComplete 𝕜 (X →Lₚₜ[𝕜] Y) := by sorry
end GarrettFA
