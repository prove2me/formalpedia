-- Prove2me | Theorems.Thm_OAI_Solenoidal_scheduledPulse_integer_collar
-- name    : OAI.Solenoidal.scheduledPulse_integer_collar
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:32:14.157925+00:00
-- url     : https://prove2.me/theorems/ffae6e90-2625-47c4-be35-1981a734180e
-- title:
--   Scheduled time pulses vanish within distance $1/4$ of every integer
-- statement:
--   Let $\psi(s)=e^{-1/s}$ for $s>0$ and $\psi(s)=0$ for $s\le0$, and let $S(s)=\psi(s)/\bigl(\psi(s)+\psi(1-s)\bigr)$ be the standard smooth transition function, which is $0$ on $(-\infty,0]$ and $1$ on $[1,\infty)$. For $a<b$ the local pulse $\ell_{a,b}(t)=\frac{d}{dt}S\bigl(\frac{t-a}{b-a}\bigr)$ is smooth and vanishes outside $(a,b)$, and its $1$-periodization is $\phi_{a,b}(t)=\sum_{k\in\mathbb{Z}}\ell_{a,b}(t-k)$. For $m\ge1$ and $i\in\{0,\dots,m-1\}$, the $i$-th scheduled pulse is $\phi_{m,i}=\phi_{a_{m,i},b_{m,i}}$, with slot endpoints
--   $$a_{m,i}=\frac14+\frac{i}{2m},\qquad b_{m,i}=a_{m,i}+\frac{1}{4m}.$$
--
--   **Theorem.** For every $m\ge1$, $i\in\{0,\dots,m-1\}$, $n\in\mathbb{Z}$ and $t\in\mathbb{R}$ with $|t-n|<\frac14$,
--   $$\phi_{m,i}(t)=0 .$$
--
--   All slots $(a_{m,i},b_{m,i})$ lie in $[\frac14,\frac34]$, so every scheduled pulse is switched off on the collars $(n-\frac14,n+\frac14)$ around the integers. Consequently any velocity field built as a combination of scheduled pulses vanishes in a neighbourhood of every integer time, and in particular at time $0$, which yields the zero initial condition and the vanishing near integer times required of the flow.
--
--   **Formalization Note** The condition $m\ge1$ is implicit, since $i$ ranges over `Fin m`. Here `scheduledPulse m i = periodicPulse (slotLeft m i) (slotRight m i)` and `periodicPulse a b = periodize 1 (localPulse a b)`, where `periodize` is an infinite sum (`tsum`) over $k\in\mathbb{Z}$ and `localPulse a b` is `deriv` of $t\mapsto S((t-a)/(b-a))$, with $S$ = `Real.smoothTransition`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/SheetFlows/Clocks.lean#L186-L203

import Mathlib
import Definitions.Def_SolenoidalSheetPrograms
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_DirectForce
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Profiles
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Clocks

open OAI OAI.Solenoidal
open Set MeasureTheory
open scoped BigOperators
open Filter
open scoped Topology

theorem OAI.Solenoidal.scheduledPulse_integer_collar {m : ℕ} (i : Fin m)
    (n : ℤ) {t : ℝ} (ht : |t - (n : ℝ)| < 1/4) :
    scheduledPulse m i t = 0 := by sorry
