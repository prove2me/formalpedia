-- Prove2me | Theorems.Thm_OAI_ArnoldCounterexample_Forms_fderiv_circle_equivariant
-- name    : OAI.ArnoldCounterexample.Forms.fderiv_circle_equivariant
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T09:31:53.090158+00:00
-- url     : https://prove2.me/theorems/45b1dc03-5609-4e18-a3e1-4e219643a5cc
-- title:
--   Circle-equivariant maps intertwine the infinitesimal circle actions: $dF(z)[iz]=iF(z)$
-- statement:
--   Let $m,n\in\mathbb{N}$, $F:\mathbb{C}^m\to\mathbb{C}^n$ real-differentiable, and $z\in\mathbb{C}^m$ such that $F(\alpha z)=\alpha F(z)$ for every $\alpha\in\mathbb{C}$ with $|\alpha|=1$. Then
--   $$
--   dF(z)[\,i z\,]=i\,F(z).
--   $$
--
--   The derivative of an equivariant map sends the generator of the circle action at $z$ to the generator at $F(z)$. This is the infinitesimal form of equivariance, derived here from the global one.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/Arnold/Volume.lean#L142-L160

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
import Definitions.Def_OAI_Geometry_Arnold_Deformation
import Definitions.Def_OAI_Geometry_Arnold_Exterior
import Definitions.Def_OAI_Geometry_Arnold_Homotopy
import Definitions.Def_OAI_Geometry_Arnold_Volume

open OAI OAI.ArnoldCounterexample OAI.ArnoldCounterexample.Forms
universe uE uF
open scoped BigOperators ContDiff
open MeasureTheory Set Filter
open scoped Matrix.Norms.Operator
open scoped Topology
open Function
open ContinuousAlternatingMap
open ContinuousAlternatingMap

theorem OAI.ArnoldCounterexample.Forms.fderiv_circle_equivariant {m n : ℕ} (F : CSpace m → CSpace n)
    (hF : Differentiable ℝ F) (z : CSpace m)
    (hphase : ∀ a : ℂ, Complex.normSq a = 1 → F (a • z) = a • F z) :
    fderiv ℝ F z (Complex.I • z) = Complex.I • F z := by sorry
