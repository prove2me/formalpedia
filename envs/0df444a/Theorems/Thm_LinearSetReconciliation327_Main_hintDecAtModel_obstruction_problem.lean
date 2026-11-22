-- Prove2me | Theorems.Thm_LinearSetReconciliation327_Main_hintDecAtModel_obstruction_problem
-- name    : LinearSetReconciliation327.Main.hintDecAtModel_obstruction_problem
-- status  : Proved
-- author  : @djwj233
-- created : 2026-11-22T08:54:13.146052+00:00
-- url     : https://prove2.me/theorems/3cc6374e-8c83-4ab0-be1e-b930b2774001
-- title:
--   The `det[3]` entry obstruction of Theorem 5.1's decoder, and the `DownBlkSem` reduction
-- statement:
--   Theorem 5.1's decoder reads its deterministic table through the absolute entry $\mathrm{det}[3]$.  For any relocation prefix followed by 5.1's decoder prologue and an arbitrary continuation, the state after the prefix and the prologue's first two instructions has $r_6=\mathrm{det}[3] \pmod{2^W}$: the prologue re-establishes $r_3=3$ before its first table read, so no prefix can select $\mathrm{det}(\delta+3)$.
--
--   The statement also records the $\beta=0$ reduction of the task's `DownBlkSem` contract: at $\mathrm{base}=\delta=\beta=0$, $\mathrm{dt}=\mathrm{det}$ and the standard `decoderStart` state, the contract yields Theorem 5.1's own halting conjunct (within the same budget), so the shape is not vacuous.  Finally, the literal shape is false at $T=0$ for every program of positive length, so any use must pin the budget positive and pin the per-child table rather than quantifying over an arbitrary `dt`.
--
--   Consequently Theorem 6.5's column stage cannot run 5.1's decoder per sub-block by a prefix: the decoder's three $\mathrm{det}[3]$ reads have to be relocated in the body, and the caller's per-child table has to rebase its pointer-valued slots.
-- source:
--   arXiv:2611.11409 (Liu, Xu, Yang, Zhou), Theorem 5.1 (decoder program) and Theorem 6.5 (column stage); the prologue is 5.1's `hintRootHintArgs`.

import Definitions.Def_LinearSetReconciliation327_Main_HintDecAtModel20261122

namespace LinearSetReconciliation327.Main

theorem hintDecAtModel_obstruction_problem (body : Stmt) :
    (∀ (G : Program) (base : ℕ) (E : RAMEnv) (s : RAMState),
      At G base ((hintDecAtModel body).compile base) → s.pc = base → 3 < 2 ^ E.W →
      ((step G E)^[hintDecPre.length + 2] s).regs 6 = E.det 3 % 2 ^ E.W) ∧
    (∀ {Sdec : Stmt} {E : RAMEnv} {T : ℝ} {Bw N Ms : ℕ}
      {Hs : (Fin N → ZMod 2) →ₗ[ZMod 2] (Fin Ms → ZMod 2)},
      DownBlkSem Sdec E T Bw Hs → Bw ≤ 2 ^ E.W → wordsOf E.W Ms ≤ 2 ^ E.W →
      ∀ (y : Fin Ms → ZMod 2) (J : List ℕ),
        ∃ s', HaltsWithin (Sdec.compile 0 ++ [Instr.halt]) E T (decoderStart E.W y J) s') ∧
    (∀ {Sdec : Stmt} {E : RAMEnv} {Bw N Ms : ℕ}
      {Hs : (Fin N → ZMod 2) →ₗ[ZMod 2] (Fin Ms → ZMod 2)},
      0 < Sdec.len → Bw ≤ 2 ^ E.W → wordsOf E.W Ms ≤ 2 ^ E.W →
      ¬ DownBlkSem Sdec E 0 Bw Hs) := by sorry

end LinearSetReconciliation327.Main
