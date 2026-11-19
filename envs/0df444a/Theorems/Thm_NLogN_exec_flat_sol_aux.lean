-- Prove2me | Theorems.Thm_NLogN_exec_flat_sol_aux
-- name    : NLogN.exec_flat_sol_aux
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T08:10:38.787683+00:00
-- url     : https://prove2.me/theorems/38c8757c-6681-44cc-a340-b7cd4221055b
-- title:
--   Exact-step simulation of structured programs by placed flat instruction code
-- statement:
--   Let a structured finite-stack program have its procedures correctly placed in flat instruction code, with procedure entry addresses fixed. Suppose a structured statement $P$ executes from stack state $\sigma$ to $\sigma'$ in exactly $c$ steps, and its code occupies entry and exit addresses $a,e$. Then, for every existing control stack $C$,
--   $$\langle a,\sigma,C\rangle\xrightarrow[c]{\rm flat}\langle e,\sigma',C\rangle.$$
--   Both executions use the same input list and data stacks. The statement includes primitive stack and input-output operations, sequencing, conditional branches, loops, and procedure calls. The existing control stack is restored. This exact-step compiler theorem connects the structured bit-level program proofs to instruction-machine execution without adding an unaccounted simulation factor.
-- source:
--   T. Koana, Approximate Counting of k-Paths in O*(2^k) Time, STOC 2027 submission #953, October 2026, §3.2 (printed pp. 8–9 / PDF pp. 9–10) and §4.1 (printed p. 9 / PDF p. 10), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/953.pdf. Native implementation: Solutions/FlatCompiler.lean, line 36; source snapshot SHA-256 aa2df6c91da3ceeb506f695a6e263b601c5e629a3216f3933565e9c8154da402.

import Definitions.Def_IntMul_SS_Defs1
import Definitions.Def_KoanaKPaths_Runtime_LiftNative
import Definitions.Def_KoanaKPaths_Runtime_NatParser
import Definitions.Def_KoanaKPaths_Runtime_NativeProgram
import Definitions.Def_KoanaKPaths_Runtime_SubsetArrays
import Definitions.Def_KoanaKPaths_Runtime_TrialIndexing
import Mathlib
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem NLogN.exec_flat_sol_aux :
∀ {S P : Nat} {I : List.{0} NLogN.Sym} {prog : Fin P → NLogN.Stmt S P} {code : Nat → NLogN.Instr S} {ent : Fin P → Nat}
  (hprog : @NLogN.ProgPlaced S P code prog ent) {s : NLogN.Stmt S P} {σ σ' : NLogN.St S} {c : Nat}
  (h : @NLogN.Exec S P I prog s σ σ' c) (a e : Nat),
  @NLogN.Placed S P code ent s a e →
    ∀ (ctl : List.{0} Nat), @NLogN.Steps S I code (@NLogN.Cfg.mk S a σ ctl) c (@NLogN.Cfg.mk S e σ' ctl) := by sorry
