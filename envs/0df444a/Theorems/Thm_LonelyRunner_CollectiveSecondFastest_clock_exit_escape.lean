-- Prove2me | Theorems.Thm_LonelyRunner_CollectiveSecondFastest_clock_exit_escape
-- name    : LonelyRunner.CollectiveSecondFastest.clock_exit_escape
-- status  : Proved
-- author  : @Whunt003
-- created : 2026-10-07T06:04:46.281263+00:00
-- url     : https://prove2.me/theorems/9270011a-94f6-45b5-87e6-4731b7b308a5
-- title:
--   Strict inequalities persist after a common half-phase exit
-- statement:
--   Write $d(x)=|x-\operatorname{round}(x)|$ for distance to the nearest integer. Let $n,P,Q,\gamma,z_0,T\in\mathbb R$, $A,J,j\in\mathbb Z$, $S\subseteq\mathbb N$ be finite, and $c:\mathbb R\to\mathbb R$ continuous. Assume $n>2$, $\gamma>0$, $1\le z_0<n-1$, $\gamma z_0=T+1$, $T=n(j+1/2)$, and, for every real $z$, $Pc(z)=A-z/n$ and $Qc(z)=J+1/2-\gamma z/n$. If $d(vc(z_0))>1/n$ for every $v\in S$, then some $z>z_0$ satisfies these strict inequalities for all $v\in S$ and also for $P$ and $Q$.
-- source:
--   Wade Hunter, lonely-runner research repository, https://github.com/huntrontrakkr/lonely-runner; local source snapshot 9b5f51aa235e321a3ec794c9bf60358933a8e6dc, lean/LonelyRunner/CollectiveSecondFastest.lean, lines 54–118, declaration LonelyRunner.CollectiveSecondFastest.clock_exit_escape. AI-assisted formalization. The snapshot identifier records the submitted local source; it is not a claim that this commit is publicly hosted.

import Mathlib
import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.Index
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Int.Basic
import Definitions.Def_LRC_SharedRepair_Defs

open LonelyRunner
open LonelyRunner.CollectiveSecondFastest
open BadCover

/-- Strict inequalities at finitely many speeds persist on a small rightward
clock interval. Both distinguished runners become safe immediately after the
common exit. -/
theorem LonelyRunner.CollectiveSecondFastest.clock_exit_escape {n P Q gamma z₀ T : ℝ} {A J j : ℤ}
    (S : Finset ℕ) (clock : ℝ → ℝ) (hclock : Continuous clock)
    (hn : 2 < n) (hg : 0 < gamma)
    (hz : 1 ≤ z₀) (hzupper : z₀ < n-1)
    (he : gamma*z₀=T+1) (hT : T=n*((j:ℝ)+1/2))
    (hP : ∀ z, P*clock z=(A:ℝ)-z/n)
    (hQ : ∀ z, Q*clock z=(J:ℝ)+1/2-gamma*z/n)
    (hsafe : ∀ v ∈ S, 1/n < ndist ((v:ℝ)*clock z₀)) :
    ∃ z, z₀ < z ∧ 1/n < ndist (P*clock z) ∧
      1/n < ndist (Q*clock z) ∧ ∀ v ∈ S, 1/n < ndist ((v:ℝ)*clock z) := by sorry
