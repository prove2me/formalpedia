-- Prove2me | Theorems.Thm_OAI_Solenoidal_scheduleVelocity_at_time
-- name    : OAI.Solenoidal.scheduleVelocity_at_time
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:32:51.361755+00:00
-- url     : https://prove2.me/theorems/db1f949f-4c55-4362-af62-d1bf06edb07c
-- title:
--   At each time a scheduled velocity has at most one active pulse
-- statement:
--   Fix $m\in\mathbb{N}$. Let $\psi(s)=e^{-1/s}$ for $s>0$ and $\psi(s)=0$ for $s\le0$, and let $S(s)=\psi(s)/\bigl(\psi(s)+\psi(1-s)\bigr)$ be the standard smooth transition function, which is $0$ on $(-\infty,0]$ and $1$ on $[1,\infty)$. For $a<b$ the local pulse $\ell_{a,b}(t)=\frac{d}{dt}S\bigl(\frac{t-a}{b-a}\bigr)$ is smooth and vanishes outside $(a,b)$, and its $1$-periodization is $\phi_{a,b}(t)=\sum_{k\in\mathbb{Z}}\ell_{a,b}(t-k)$. For $i\in\{0,\dots,m-1\}$ the $i$-th scheduled pulse is $\phi_{m,i}=\phi_{a_{m,i},b_{m,i}}$, with slot endpoints $a_{m,i}=\frac14+\frac{i}{2m}$ and $b_{m,i}=a_{m,i}+\frac{1}{4m}$.
--
--   Let $v_0,\dots,v_{m-1}:\mathbb{R}^3\to\mathbb{R}^3$ be arbitrary maps (no regularity is assumed). The scheduled velocity is the time-dependent field
--   $$U(t,x)=\sum_{i=0}^{m-1}\phi_{m,i}(t)\,v_i(x).$$
--
--   **Theorem.** For every $t\in\mathbb{R}$, either $U(t,x)=0$ for all $x\in\mathbb{R}^3$, or there is an index $i\in\{0,\dots,m-1\}$ such that
--   $$U(t,x)=\phi_{m,i}(t)\,v_i(x)\qquad\text{for all }x\in\mathbb{R}^3 .$$
--
--   The slots $(a_{m,i},b_{m,i})$ are pairwise disjoint subintervals of $[\frac14,\frac34]$, so the scheduled velocity runs the stationary fields $v_0,\dots,v_{m-1}$ one at a time, in this order, during each unit time interval. The reduction to a single active field transfers pointwise properties of the $v_i$, such as zero divergence and vanishing self-advection $Dv_i(x)[v_i(x)]=0$, to $U$ at every time.
--
--   **Formalization Note** `scheduleVelocity v t x = ∑ i, scheduledPulse m i t • v i x`, and the statement is an equality of functions `Space → Space` at the fixed time `t`. For $m=0$ the sum is empty and the first alternative holds.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/SheetFlows/Differential.lean#L70-L85

import Mathlib
import Definitions.Def_SolenoidalSheetPrograms
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_DirectForce
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Profiles
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Clocks
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Differential

open OAI OAI.Solenoidal
open Set MeasureTheory
open scoped BigOperators
open Filter
open scoped Topology

theorem OAI.Solenoidal.scheduleVelocity_at_time {m : ℕ} (v : Fin m → Space → Space) (t : ℝ) :
    scheduleVelocity v t = 0 ∨
      ∃ i, scheduleVelocity v t = scheduledPulse m i t • v i := by sorry
