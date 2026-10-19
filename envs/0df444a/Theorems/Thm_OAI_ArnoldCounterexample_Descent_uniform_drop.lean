-- Prove2me | Theorems.Thm_OAI_ArnoldCounterexample_Descent_uniform_drop
-- name    : OAI.ArnoldCounterexample.Descent.uniform_drop
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T09:22:14.782975+00:00
-- url     : https://prove2.me/theorems/464f478a-cd02-4ea3-9e56-316a07e69671
-- title:
--   A compact band without stationary points is crossed in a uniform number of steps
-- statement:
--   Let $X$ be a compact topological space, $D:X\to X$ continuous and $f:X\to\mathbb{R}$ continuous, with $f(Dx)\le f(x)$ for all $x$. Let $a,b\in\mathbb{R}$, and suppose $f(Dx)<f(x)$ whenever $a\le f(x)\le b$. Then there is $N\in\mathbb{N}$ such that
--   $$
--   f(x)\le b\ \Longrightarrow\ f\bigl(D^Nx\bigr)<a .
--   $$
--
--   A Lyapunov map with no stationary points in the closed band $\{a\le f\le b\}$ pushes the whole sublevel set $\{f\le b\}$ below $a$ in a uniform number of iterations. This is the deformation step of the Lusternik–Schnirelmann-type argument.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/Arnold/Descent.lean#L107-L144

import Mathlib
import Definitions.Def_ArnoldCounterexample
import Definitions.Def_OAI_Geometry_Arnold_Involution
import Definitions.Def_OAI_Geometry_Arnold_Projective
import Definitions.Def_OAI_Geometry_Arnold_Rotation
import Definitions.Def_OAI_Geometry_Arnold_Tangent
import Definitions.Def_OAI_Geometry_Arnold_Haar
import Definitions.Def_OAI_Geometry_Arnold_Differentiation
import Definitions.Def_OAI_Geometry_Arnold_Orbit
import Definitions.Def_OAI_Geometry_Arnold_Symplectic
import Definitions.Def_OAI_Geometry_Arnold_Coordinates
import Definitions.Def_OAI_Geometry_Arnold_Extension

open OAI OAI.ArnoldCounterexample
universe uE uX
open scoped BigOperators ContDiff
open MeasureTheory Set Filter
open scoped Matrix.Norms.Operator
open scoped Topology
open Set
open scoped ContDiff
open Set Function
variable {X : Type uX} [TopologicalSpace X] [CompactSpace X]

theorem OAI.ArnoldCounterexample.Descent.uniform_drop {D : X → X} {f : X → ℝ}
    (hD : Continuous D) (hf : Continuous f)
    (hdec : ∀ x, f (D x) ≤ f x) (a b : ℝ)
    (hstrict : ∀ x, a ≤ f x → f x ≤ b → f (D x) < f x) :
    ∃ N : ℕ, ∀ x, f x ≤ b → f (D^[N] x) < a := by sorry
