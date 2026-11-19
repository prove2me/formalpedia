-- Prove2me | Theorems.Thm_Lax263307Proofs_NativeNodeExecution_executes
-- name    : Lax263307Proofs.NativeNodeExecution.executes
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T12:10:21.438328+00:00
-- url     : https://prove2.me/theorems/ac379917-9d88-433a-b1ba-c0f2bb9f64ef
-- title:
--   Execution of every eligible recursive MWIS node
-- statement:
--   Fix a native core configuration, the chosen LP and flow functions, array extents, and an eligibility predicate. Let $D,S,v,w$ denote the precision denominator, frame stride, virtual word width and host word width. Suppose the published resource contract holds with local step bound $s_0$, local time bound $t_0$, and branching bound $b$.
--
--   For every recursion fuel $f$, every eligible node has the complete operational execution promised by the node protocol, with step and time bounds
--   $$s\le W(s_0,b,f),\qquad t\le W(t_0,b,f),$$
--   where $W(c,b,0)=c$ and $W(c,b,f+1)=c+bW(c,b,f)$. The protocol includes the returned answer, graph and stack-frame invariants and the actual return phase. This theorem converts uniform local resource data into executions of the entire bounded recursion.
-- source:
--   https://github.com/EdouardBonnet/lax-263307/blob/68b2d26aa2075e2ef80fd9d355ea748d2a818fd1/proofs/Lax263307Proofs/NativeNodeExecution.lean, theorem executes

import Definitions.Def_EdgeSublinearMWIS_Main_NativeCertificateInterfaces

theorem Lax263307Proofs.NativeNodeExecution.executes : ∀ (D S v w localSteps localTime branches : ℕ) (cfg : Lax263307Proofs.NativeCoreMachine.Config)
  (lp flow : List ℕ → List ℕ) (extent : String → ℕ) (eligible : Lax263307Proofs.NativeNodeProtocol.Eligible)
  (resources :
    Lax263307Proofs.NativeNodeExecution.Resources D S v w localSteps localTime branches cfg lp flow extent eligible)
  (fuel : ℕ),
  Lax263307Proofs.NativeNodeProtocol.Executes (2 ^ w) D fuel S v
    (Lax263307Proofs.NativeRecursionBudget.work localSteps branches fuel)
    (Lax263307Proofs.NativeRecursionBudget.work localTime branches fuel) cfg lp flow extent eligible := by sorry
