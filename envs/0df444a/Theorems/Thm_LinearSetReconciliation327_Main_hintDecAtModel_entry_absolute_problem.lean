-- Prove2me | Theorems.Thm_LinearSetReconciliation327_Main_hintDecAtModel_entry_absolute_problem
-- name    : LinearSetReconciliation327.Main.hintDecAtModel_entry_absolute_problem
-- status  : Proved
-- author  : @djwj233
-- created : 2026-11-22T08:51:28.904379+00:00
-- url     : https://prove2.me/theorems/34b56dcb-5b16-4b0b-bf45-4dacb07a4ed7
-- title:
--   A prefix cannot relocate Theorem 5.1's decoder `det[3]` entry
-- statement:
--   Theorem 5.1's word-RAM decoder locates its deterministic table through the absolute entry $\mathrm{det}[3]$: its prologue executes $r_3\leftarrow 3$ and $r_6\leftarrow \mathrm{det}[r_3]$, so $r_6$ becomes the header address $h=\mathrm{det}[3]$, and every later table access is either $\mathrm{det}(h+k)$ or at a pointer value stored in the table.  If a relocation prefix writes $3+\delta$ into $r_3$ and $\beta+\mathrm{wordsOf}$ into $r_1$ before the prologue, the prologue's own $r_3\leftarrow 3$ overwrites the entry: after the prefix and the first two prologue instructions the header register is still $\mathrm{det}[3]$, independently of $\delta$.  Hence no prefix can make the decoder read $\mathrm{det}(\delta+3)$; the three $\mathrm{det}[3]$ reads have to be edited in the body, exactly as Proposition 2.3's `cr23UpPreAt` inserts $r_5\leftarrow r_5+\delta$ after its table read rather than merely prefixing.  This is the obstruction that stops Theorem 6.5's column stage from running the unmodified 5.1 decoder per sub-block.
-- source:
--   Theorem 5.1 and Theorem 6.5 of arXiv:2611.11409 (Liu--Xu--Yang--Zhou, *Linear Set Reconciliation with O(d) Additive Redundancy*); the prologue is 5.1's `hintRootHintArgs`.

import Definitions.Def_LinearSetReconciliation327_Main_HintDecAtModel20261122

namespace LinearSetReconciliation327.Main

theorem hintDecAtModel_entry_absolute_problem
    (body : Stmt) (G : Program) (base : ℕ) (E : RAMEnv) (s : RAMState)
    (hAt : At G base ((hintDecAtModel body).compile base))
    (hpc : s.pc = base) (hW : 3 < 2 ^ E.W) :
    ((step G E)^[hintDecPre.length + 2] s).regs 6 = E.det 3 % 2 ^ E.W := by sorry

end LinearSetReconciliation327.Main
