-- Prove2me | Theorems.Thm_OAI_Solenoidal_travelProgram_on
-- name    : OAI.Solenoidal.travelProgram_on
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:42:59.334087+00:00
-- url     : https://prove2.me/theorems/3e469f27-cac7-41bc-b04f-e116893b5d48
-- title:
--   Two horizontal pulses translate the plane $x_2=5$ by an arbitrary horizontal vector
-- statement:
--   Fix a collar width $d$ with $0<d\le\frac1{10}$. Let $\psi(x)=e^{-1/x}$ for $x>0$ and $\psi(x)=0$ for $x\le0$, let $S(x)=\psi(x)/\big(\psi(x)+\psi(1-x)\big)$ be the standard smooth step, and let
--   $$C_{c}(x)=\sum_{k\in\mathbb{Z}}\varphi(x-10k-c),\qquad \varphi(s)=S\Big(\frac{2(s+d)}{d}\Big)\,S\Big(\frac{2(d-s)}{d}\Big),$$
--   be the $10$-periodization, centered at $c$, of a smooth bump $\varphi$ that equals $1$ for $|s|\le\frac d2$ and $0$ for $|s|\ge d$. For $j\in\{0,1\}$ the horizontal pulse is the vector field
--   $$H_j(x)=\big(C_5(x_2)-C_8(x_2)\big)\,e_j\qquad(x\in\mathbb{R}^3),$$
--   with $e_0,e_1$ the horizontal unit vectors. A pulse $V$ acts on a point by $a\mapsto a+V(a)$, and a program, a finite list of pulses, acts by applying its pulses in order. For $\delta=(\delta_0,\delta_1)\in\mathbb{R}^2$ the travel program is the list $(\delta_0H_0,\ \delta_1H_1)$.
--
--   **Theorem.** For every $\delta\in\mathbb{R}^2$ and all $x,y\in\mathbb{R}$, running the travel program on $(x,y,5)$ gives
--
--   $$
--   \big(\mathrm{id}+\delta_1H_1\big)\circ\big(\mathrm{id}+\delta_0H_0\big)\,(x,y,5)=(x+\delta_0,\;y+\delta_1,\;5).
--   $$
--
--   On the plane $x_2=5$ each horizontal pulse coincides with its unit vector, so the two-step program moves this plane rigidly by an arbitrary horizontal vector while keeping it at height $5$. Since each pulse field is constant along its own straight lines, $a+V(a)$ is also the position reached by flowing along $V$ for unit time, so the program describes how a sheet parked at height $5$ is transported horizontally.
--
--   **Formalization Note** `horizontalPulse d j` is a `StationaryPulse` (smooth, periodic, mean zero, divergence free) whose field is the formula above, `p.scale c` multiplies the field by $c$, `StationaryPulse.apply` is $a\mapsto a+V(a)$, and `runProgram` is a left fold over the list. Coordinates are indexed from $0$, so $x_2$ is the vertical coordinate.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/SheetFlows/Localization.lean#L292-L304

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
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Trajectories
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Pulses
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Localization

open OAI OAI.Solenoidal
open Set MeasureTheory
open scoped BigOperators
variable (d : Collar)

theorem OAI.Solenoidal.travelProgram_on (δ : Plane) (x y : ℝ) :
    runProgram (travelProgram d δ) ![x,y,5] = ![x+δ 0,y+δ 1,5] := by sorry
