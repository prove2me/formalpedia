-- Prove2me | Theorems.Thm_OpenGA_SurgeryContinuationData_definedUpTo_of_locallyFinite
-- name    : OpenGA.SurgeryContinuationData.definedUpTo_of_locallyFinite
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-10T18:33:14.855401+00:00
-- url     : https://prove2.me/theorems/b726d5ea-1b21-438d-84af-7d6538782cfc
-- title:
--   All-time existence from locally finite surgery times
-- statement:
--   Let $C$ be a surgery continuation datum: a predicate $\mathrm{Def}(T)$ saying that the Ricci flow with surgery is defined on $[0,T]$, which holds at $T=0$, is downward closed, can always be prolonged past a time it reaches, and attains a limit time $T$ whenever it holds below $T$ and only finitely many surgeries occur up to $T$.
--
--   If the surgery times are locally finite, that is if the set of surgery times $\le T$ is finite for every $T$, then the flow is defined for all time:
--   $$\mathrm{Def}(T)\quad\text{for every } T\ge 0 .$$
--
--   This is the continuation argument of Kleiner–Lott, p. 147. If the set of times where definedness fails were nonempty, its infimum $T_*$ would be attained by the limit mechanism, and prolongation past $T_*$ would contradict its minimality.
--
--   Only local finiteness of the set of surgery times is used, which is what the volume estimates supply on each finite horizon; global finiteness of the set of surgery times, which does not hold in general for a flow defined on all of $[0,\infty)$, is not assumed.
-- source:
--   Kleiner-Lott, Notes on Perelman's papers, https://arxiv.org/abs/math/0605667, Lemma 73.7 (p. 140) and Section 77, p. 147

import Definitions.Def_OpenGA_SurgeryContinuationData

set_option autoImplicit false
open Set

theorem OpenGA.SurgeryContinuationData.definedUpTo_of_locallyFinite
    (C : OpenGA.SurgeryContinuationData)
    (hfin : ∀ T : ℝ, (C.surgeryTimes ∩ Iic T).Finite) (T : ℝ) (hT : 0 ≤ T) :
    C.DefinedUpTo T := by sorry
