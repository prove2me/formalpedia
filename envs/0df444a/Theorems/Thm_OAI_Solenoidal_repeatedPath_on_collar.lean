-- Prove2me | Theorems.Thm_OAI_Solenoidal_repeatedPath_on_collar
-- name    : OAI.Solenoidal.repeatedPath_on_collar
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:41:28.19299+00:00
-- url     : https://prove2.me/theorems/3bf63906-4aae-4fce-b946-706751a13e15
-- title:
--   The repeated launch path is constant near every integer time $n$, equal to the $n$-th period state
-- statement:
--   Fix $m\in\mathbb{N}$, maps $v_0,\dots,v_{m-1}:\mathbb{R}^3\to\mathbb{R}^3$ and a starting point $a\in\mathbb{R}^3$.
--
--   *Stages.* For $b\in\mathbb{R}^3$ define the stage states $b_0=b$, $b_{k+1}=b_k+v_k(b_k)$ for $k<m$, and the increments $\Delta_i(b)=v_i(b_i)$ for $0\le i<m$. The *period states* are $P_0=a$ and $P_{n+1}=(P_n)_m$, the point reached from $P_n$ after one full cycle of the $m$ stages.
--
--   *Clocks.* Let $\psi(x)=e^{-1/x}$ for $x>0$ and $\psi(x)=0$ for $x\le0$, and let $S(x)=\psi(x)/\big(\psi(x)+\psi(1-x)\big)$ be the standard smooth step, equal to $0$ on $(-\infty,0]$ and to $1$ on $[1,\infty)$. For $i<m$ put
--   $$\ell_i=\frac14+\frac{i}{2m},\qquad r_i=\ell_i+\frac1{4m},\qquad \chi_i(\tau)=S\Big(\frac{\tau-\ell_i}{r_i-\ell_i}\Big);$$
--   the slots $[\ell_i,r_i]$ are pairwise disjoint, ordered by $i$, and contained in $[\frac14,\frac34]$.
--
--   *Paths.* The launch path from $b$ is $L_b(\tau)=b+\sum_{i<m}\chi_i(\tau)\,\Delta_i(b)$, and the repeated path is $\gamma(t)=L_{P_{N(t)}}\big(t-N(t)\big)$, where $N(t)=\lfloor t\rfloor$ for $t\ge0$ and $N(t)=0$ for $t<0$ (the natural-number floor).
--
--   **Theorem.** For every $n\in\mathbb{N}$ and every real $t$ with $|t-n|<\frac14$,
--
--   $$
--   \gamma(t)=P_n .
--   $$
--
--   The repeated path performs, during each unit time interval, the $m$ stages one after another in disjoint time slots inside $[\frac14,\frac34]$, and is at rest in the collars $|t-n|<\frac14$ around integer times. The theorem shows that the pieces glue across integer times and that at (and near) time $n$ the point has completed exactly $n$ full cycles, matching velocity fields that vanish near integer times. For $n=0$ the statement also covers negative times $t\in(-\frac14,0)$.
--
--   **Formalization Note** $\gamma$ is `repeatedPath v a`, $P_n$ is `periodState v a n`, $L_b$ is `launchPath v b`, $\chi_i$ is `pulseClock (slotLeft m i) (slotRight m i)` built from Mathlib's `Real.smoothTransition`, and $N(t)$ is `⌊t⌋₊`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/SheetFlows/Trajectories.lean#L163-L181

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

open OAI OAI.Solenoidal
open Set MeasureTheory
open scoped BigOperators
open Filter
open scoped Topology

theorem OAI.Solenoidal.repeatedPath_on_collar {m : ℕ} (v : Fin m → Space → Space) (a : Space)
    (n : ℕ) {t : ℝ} (ht : |t - (n : ℝ)| < 1/4) :
    repeatedPath v a t = periodState v a n := by sorry
