-- Prove2me | Theorems.Thm_OAI_ArnoldCounterexample_Descent_thicken_sublevel
-- name    : OAI.ArnoldCounterexample.Descent.thicken_sublevel
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T09:22:46.447247+00:00
-- url     : https://prove2.me/theorems/d4739936-e652-41cc-ae41-03a2cbe77385
-- title:
--   A strict sublevel containment on a zero set persists on a slightly larger sublevel
-- statement:
--   Let $X$ be a compact topological space, $f,g:X\to\mathbb{R}$ and $\ell:X\to\mathbb{C}$ continuous, and $c,a\in\mathbb{R}$. Suppose that every $x$ with $f(x)\le c$ and $\ell(x)=0$ satisfies $g(x)<a$. Then there is $\varepsilon>0$ such that
--   $$
--   f(x)\le c+\varepsilon\ \text{ and }\ \ell(x)=0\ \Longrightarrow\ g(x)<a .
--   $$
--
--   This is the compactness argument that turns a containment on a closed sublevel set into one on a slightly larger sublevel set. It lets the induction over critical values proceed past a critical level.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/Arnold/Descent.lean#L146-L166

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

theorem OAI.ArnoldCounterexample.Descent.thicken_sublevel {f g : X → ℝ} {ℓ : X → ℂ}
    (hf : Continuous f) (hg : Continuous g) (hℓ : Continuous ℓ)
    (c a : ℝ) (h : ∀ x, f x ≤ c → ℓ x = 0 → g x < a) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x, f x ≤ c + ε → ℓ x = 0 → g x < a := by sorry
