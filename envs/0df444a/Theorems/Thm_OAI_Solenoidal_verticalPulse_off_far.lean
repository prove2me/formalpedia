-- Prove2me | Theorems.Thm_OAI_Solenoidal_verticalPulse_off_far
-- name    : OAI.Solenoidal.verticalPulse_off_far
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:42:22.502771+00:00
-- url     : https://prove2.me/theorems/a995a0c5-3d3e-4e68-9551-1b7a2c0dc9be
-- title:
--   A vertical pulse at horizontal offset $s$ vanishes on coding rectangles shifted by an offset at distance $4$
-- statement:
--   Fix a collar width $d$ with $0<d\le\frac1{10}$. Let $\psi(x)=e^{-1/x}$ for $x>0$ and $\psi(x)=0$ for $x\le0$, and let $S(x)=\psi(x)/\big(\psi(x)+\psi(1-x)\big)$ be the standard smooth step. For $h\ge0$ the plateau
--   $$\varphi_{h,d}(s)=S\Big(\frac{2(s+h+d)}{d}\Big)\,S\Big(\frac{2(h+d-s)}{d}\Big)$$
--   is a smooth even bump equal to $1$ for $|s|\le h+\frac d2$ and to $0$ for $|s|\ge h+d$; its $10$-periodization centered at $c\in\mathbb{R}$ is $C_{h,d,c}(x)=\sum_{k\in\mathbb{Z}}\varphi_{h,d}(x-10k-c)$.
--
--   A rectangle $P$ has rational corners $(a_0,a_1)$, $(b_0,b_1)$ with $a_j<b_j$, center $c_j=\frac{a_j+b_j}2$, half-widths $h_j=\frac{b_j-a_j}2$, and is identified with the closed set $\{y\in\mathbb{R}^2:a_j\le y_j\le b_j\}$. It lies in the coding square if $2\le a_j$ and $b_j\le3$ for $j=0,1$. For such $P$ and a shift $s\in\mathbb{R}$ the vertical pulse of $P$ at offset $s$ is the stationary vector field on $\mathbb{R}^3$
--   $$V_{P,s}(x)=C_{h_0,d,c_0+s}(x_0)\,\Big(C_{h_1,d,c_1}(x_1)-C_{h_1,d,c_1+4}(x_1)\Big)\,e_2 ,$$
--   where $e_2=(0,0,1)$ is the vertical unit vector.
--
--   **Theorem.** Let $P$ and $Q$ be rectangles in the coding square, let $s,t\in[0,4]$ with $|t-s|\ge4$, let $y\in Q$ and $z\in\mathbb{R}$. Then
--
--   $$
--   V_{P,s}\big(y_0+t,\;y_1,\;z\big)=0 .
--   $$
--
--   Under these hypotheses necessarily $\{s,t\}=\{0,4\}$. The field $V_{P,s}$ can be nonzero only at points whose first coordinate lies, modulo $10$, within distance $d$ of the interval $[a_0+s,b_0+s]$; the theorem is the resulting non-interference property: the pulse attached to one copy of the coding square (horizontal offset $s$) leaves every point above any coding rectangle $Q$ placed at the other extreme offset $t$ untouched, at every height $z$. This separation lets pulses for the two horizontal copies act independently.
--
--   **Formalization Note** `verticalPulse d P hP s` is a `StationaryPulse`: a smooth, $10\mathbb{Z}^3$-periodic, mean-zero, divergence-free field with $(V\cdot\nabla)V=0$; the statement concerns its underlying field. The point is `lifted t z y`. The periodization is `Cprofile`, the plateau is `plateau`, and $d$ is `d.size` of a `Collar`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/SheetFlows/Localization.lean#L233-L249

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

theorem OAI.Solenoidal.verticalPulse_off_far (P Q : Rectangle) (hP : P.inCodingSquare)
    (hQ : Q.inCodingSquare) {s t : ℝ} (hs : s ∈ Set.Icc 0 4)
    (ht : t ∈ Set.Icc 0 4) (hst : 4 ≤ |t-s|) {y : Plane} (hy : y ∈ Q.carrier) (z : ℝ) :
    (verticalPulse d P hP s).field (lifted t z y) = 0 := by sorry
