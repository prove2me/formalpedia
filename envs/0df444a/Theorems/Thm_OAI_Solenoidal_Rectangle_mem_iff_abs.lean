-- Prove2me | Theorems.Thm_OAI_Solenoidal_Rectangle_mem_iff_abs
-- name    : OAI.Solenoidal.Rectangle.mem_iff_abs
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:37:52.196902+00:00
-- url     : https://prove2.me/theorems/b09765c9-f624-4dcd-b71c-0bf976177fef
-- title:
--   Membership in a closed rectangle via its center and half-widths
-- statement:
--   A rectangle $R$ in the plane is given by a rational lower corner $(a_0,a_1)$ and a rational upper corner $(b_0,b_1)$ with $a_j<b_j$ for $j=0,1$; it is identified with the closed set $\{y\in\mathbb{R}^2: a_j\le y_j\le b_j \text{ for } j=0,1\}$. Its center and half-widths are
--   $$c_j=\frac{a_j+b_j}{2},\qquad h_j=\frac{b_j-a_j}{2}\qquad(j=0,1).$$
--
--   **Theorem.** For every $y=(y_0,y_1)\in\mathbb{R}^2$,
--
--   $$
--   y\in R\iff |y_j-c_j|\le h_j\quad\text{for } j=0,1 .
--   $$
--
--   This converts the corner description of a rectangle into the center/half-width description used when rectangles are enlarged by collars and when smooth cut-off profiles centered at $c_j$ with plateau half-width $h_j$ are attached to them.
--
--   **Formalization Note** The carrier is `R.carrier`, and center and half-widths are `R.center` and `R.halfWidth`, real-valued functions on `Fin 2`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/SheetFlows/RectangleGeometry.lean#L30-L43

import Mathlib
import Definitions.Def_SolenoidalSheetPrograms
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_DirectForce
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Profiles
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Clocks
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Differential
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_ScheduledForce
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_ClassicalRegularity
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_EnergyIdentities
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_RectangleGeometry

open OAI OAI.Solenoidal OAI.Solenoidal.Rectangle
open Set MeasureTheory
open scoped BigOperators

theorem OAI.Solenoidal.Rectangle.mem_iff_abs (R : Rectangle) (y : Plane) :
    y ∈ R.carrier ↔ ∀ j, |y j - R.center j| ≤ R.halfWidth j := by sorry
