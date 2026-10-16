-- Prove2me | Theorems.Thm_OAI_PermanentBorder_PolarAnalysis_simple_after_elimination
-- name    : OAI.PermanentBorder.PolarAnalysis.simple_after_elimination
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:36:31.961668+00:00
-- url     : https://prove2.me/theorems/6e1c4ff0-d492-4a2b-ac6d-6d5e64cf01e8
-- title:
--   Eliminating solvable auxiliary equations preserves invertibility of the derivative
-- statement:
--   Let $V$ and $W$ be finite-dimensional complex normed spaces, let $R:V\times W\to V$, $E:V\times W\to W$ and $g:V\to W$ be maps, and let $x\in V$. Assume that
--
--   1. $R$ and $E$ are complex differentiable at $(x,g(x))$, and $g$ is complex differentiable at $x$;
--   2. the auxiliary equations are solved by the graph of $g$ near $x$: $E(y,g(y))=0$ for all $y$ in a neighbourhood of $x$;
--   3. the partial derivative of $E$ in the $W$-direction, $D_2E(x,g(x))=DE(x,g(x))\circ\iota_2:W\to W$ with $\iota_2(w)=(0,w)$, is invertible;
--   4. the reduced map $y\mapsto R(y,g(y))$ has invertible derivative $V\to V$ at $x$.
--
--   Then the full map $(R,E):V\times W\to V\times W$, $z\mapsto(R(z),E(z))$, has invertible derivative at $(x,g(x))$:
--
--   $$
--   D(R,E)\big(x,g(x)\big)\ \text{ is a linear isomorphism of } V\times W .
--   $$
--
--   This is a linear-algebra form of variable elimination: if extra unknowns $w$ are determined by $y$ through nondegenerate auxiliary equations $E=0$, then nondegeneracy of the reduced system $y\mapsto R(y,g(y))$ at $x$ implies nondegeneracy of the enlarged system at $(x,g(x))$. It is used to show that adjoining the kernel vectors of a matrix as new unknowns keeps simple zeros simple. No vanishing of $R$ is assumed; the statement concerns derivatives only.
--
--   **Formalization Note** Invertibility is `ContinuousLinearMap.IsInvertible` of `fderiv ℂ`, i.e. the derivative is given by a continuous linear equivalence; the partial derivative is `fderiv ℂ E (x, g x) ∘L ContinuousLinearMap.inr ℂ V W`, and the neighbourhood condition is an eventual equality in the neighbourhood filter of $x$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/Determinantal/KernelCharts.lean#L363-L382

import Mathlib
import Definitions.Def_SmoothInitialForm
import Definitions.Def_OAI_Algebra_Determinantal_Multigraded
import Definitions.Def_OAI_Algebra_Determinantal_LinearForms
import Definitions.Def_OAI_Algebra_Determinantal_PointBounds
import Definitions.Def_OAI_Algebra_Determinantal_ProjectiveCounts
import Definitions.Def_OAI_Algebra_Determinantal_KernelCharts

open OAI OAI.PermanentBorder OAI.PermanentBorder.PolarAnalysis
open Filter
open scoped Topology
variable {V W : Type*}
  [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]

theorem OAI.PermanentBorder.PolarAnalysis.simple_after_elimination {R : V × W → V} {E : V × W → W}
    {g : V → W} {x : V}
    (hR : DifferentiableAt ℂ R (x,g x)) (hE : DifferentiableAt ℂ E (x,g x))
    (hg : DifferentiableAt ℂ g x)
    (he : (fun y => E (y,g y)) =ᶠ[𝓝 x] 0)
    (haux : (fderiv ℂ E (x,g x) ∘L ContinuousLinearMap.inr ℂ V W).IsInvertible)
    (hs : (fderiv ℂ (fun y => R (y,g y)) x).IsInvertible) :
    (fderiv ℂ (fun z => (R z,E z)) (x,g x)).IsInvertible := by sorry
