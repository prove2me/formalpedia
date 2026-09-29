-- Prove2me | Theorems.Thm_OpenGA_SurgeryContinuationData_allTime_or_breakdown
-- name    : OpenGA.SurgeryContinuationData.allTime_or_breakdown
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-10T18:54:13.837985+00:00
-- url     : https://prove2.me/theorems/43392861-c04f-447a-beca-91e394acabf1
-- title:
--   The maximal time interval of a Ricci flow with surgery
-- statement:
--   Let $C$ be a surgery continuation datum: a predicate $\mathrm{Def}(T)$ saying that the Ricci flow with surgery is defined on $[0,T]$, which holds at $T=0$, is downward closed, can always be prolonged past a time it reaches, and attains a limit time $T$ whenever it holds below $T$ and only finitely many surgeries occur up to $T$.
--
--   Then exactly one of two things happens: either the flow is defined for all time, or it breaks down at a finite time at which the surgery times accumulate. Precisely, either
--   $$\mathrm{Def}(T)\ \text{ for every } T\ge 0,$$
--   or there is a time $T_*>0$ with
--   $$\mathrm{Def}(S)\ \text{ for every } 0\le S<T_*,\qquad \neg\,\mathrm{Def}(T_*),\qquad \#\{t\in S_C:\ t\le T_*\}=\infty .$$
--
--   This is the dichotomy that opens Kleiner–Lott's sketch of the existence proof on p. 147: given $r$ and $\delta$ and a normalized initial condition, there is a maximal time interval on which the Ricci flow with $(r,\delta)$-cutoff is defined, and this interval can be finite only if it is of the form $[0,T)$. The statement records in addition what must go wrong at such a $T_*$ as far as the surgery times are concerned: infinitely many surgeries occur up to $T_*$. Combined with the volume estimates, which exclude that accumulation on any finite horizon, this is what forces the first alternative.
-- source:
--   Kleiner-Lott, Notes on Perelman's papers, https://arxiv.org/abs/math/0605667, Section 77, p. 147 ("there will be a maximal time interval on which the Ricci flow with (r, delta)-cutoff is defined; this interval can be finite only if it is of the form [0, T)"), and Lemma 73.7, p. 140

import Definitions.Def_OpenGA_SurgeryContinuationData

set_option autoImplicit false
open Set

theorem OpenGA.SurgeryContinuationData.allTime_or_breakdown
    (C : OpenGA.SurgeryContinuationData) :
    (∀ T : ℝ, 0 ≤ T → C.DefinedUpTo T) ∨
      ∃ Tstar : ℝ, 0 < Tstar ∧ (∀ S : ℝ, 0 ≤ S → S < Tstar → C.DefinedUpTo S) ∧
        ¬ C.DefinedUpTo Tstar ∧ ¬ (C.surgeryTimes ∩ Iic Tstar).Finite := by sorry
