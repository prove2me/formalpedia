-- Prove2me | Theorems.Thm_OAI_Solenoidal_verticalPulse_formula
-- name    : OAI.Solenoidal.verticalPulse_formula
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:47:48.329459+00:00
-- url     : https://prove2.me/theorems/28492621-4ec7-466a-8750-e49322a5401c
-- title:
--   Vertical pulses with rational collar, rectangle and offset admit explicit symbolic formulas
-- statement:
--   Let $\psi(x)=e^{-1/x}$ for $x>0$ and $\psi(x)=0$ for $x\le0$, and $S(x)=\psi(x)/\big(\psi(x)+\psi(1-x)\big)$. Fix a collar width $d$ with $0<d\le\frac1{10}$ and $d\in\mathbb{Q}$. For $h\ge0$ and $c\in\mathbb{R}$ let $\varphi_{h,d}(s)=S\big(2(s+h+d)/d\big)\,S\big(2(h+d-s)/d\big)$ (a smooth bump equal to $1$ for $|s|\le h+\frac d2$ and $0$ for $|s|\ge h+d$) and $C_{h,d,c}(x)=\sum_{k\in\mathbb{Z}}\varphi_{h,d}(x-10k-c)$. For a rectangle $R$ with rational corners $(a_0,a_1)$, $(b_0,b_1)$, $a_j<b_j$, lying in the coding square ($2\le a_j$, $b_j\le3$), with center $c_j=\frac{a_j+b_j}2$ and half-widths $h_j=\frac{b_j-a_j}2$, and for $s\in\mathbb{R}$, the vertical pulse is
--   $$V_{R,s}(x)=C_{h_0,d,c_0+s}(x_0)\,\Big(C_{h_1,d,c_1}(x_1)-C_{h_1,d,c_1+4}(x_1)\Big)\,e_2 .$$
--
--   Jet expressions, box expressions and rational formulas are as follows. A jet expression is a finite one-variable expression built from rational constants, the variable, sums, products, rational affine substitutions $x\mapsto ax+b$, the flat functions $p(1/x)\,\psi(x)$ with $p\in\mathbb{Q}[X]$, and $\rho(x)=1/\big(\psi(x)+\psi(1-x)\big)$. A box expression is a finite expression in $z=(t,x_0,x_1,x_2)$ built from rational constants, jet expressions applied to a single coordinate of $z$, sums and products. A field has a rational formula if its three components coincide on $[0,1]\times[0,10]^3$ with the values of three box expressions.
--
--   **Theorem.** Let $d\in\mathbb{Q}$ be as above, let $R$ be a rectangle in the coding square, and let $s\in[0,4]$ be rational. Then the time-independent field $(t,x)\mapsto V_{R,s}(x)$ has a rational formula: there are box expressions $F_0,F_1,F_2$ with
--
--   $$
--   V_{R,s}(x)=\big([\![F_0]\!](t,x),\,[\![F_1]\!](t,x),\,[\![F_2]\!](t,x)\big)\qquad\text{for all }(t,x)\in[0,1]\times[0,10]^3 .
--   $$
--
--   With rational data the pulses that lift the sheets are therefore given on the period cell by finite symbolic expressions over $\mathbb{Q}$, which is what makes their values and derivatives computable by exact rational interval arithmetic.
--
--   **Formalization Note** The hypotheses on $d$ are bundled as a `Collar` together with `RationalParameter d.size`, i.e. $d$ is the image of a rational; rationality of $s$ is `RationalParameter s`. The conclusion `(verticalPulse d R hR s).RationalFormula` means `HasRationalFormula (fun _ => V)` for the underlying field $V$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/SheetFlows/FormulaProfiles.lean#L90-L104

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
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_ShearCore
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Routing
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_JetCalculus
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_JetProfiles
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_BoxJets
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_RationalFormula
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_FormulaProfiles

open OAI OAI.Solenoidal
open Set MeasureTheory
open scoped BigOperators
variable (d : Collar) (hd : RationalParameter d.size)
include hd

theorem OAI.Solenoidal.verticalPulse_formula (R : Rectangle) (hR : R.inCodingSquare) {s : ℝ}
    (hs : s ∈ Set.Icc 0 4) (hsr : RationalParameter s) :
    (verticalPulse d R hR s).RationalFormula := by sorry
