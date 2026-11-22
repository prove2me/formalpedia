-- Prove2me | Theorems.Thm_LinearSetReconciliation327_Main_cr23UpStmtAt_crSemAtW_export
-- name    : LinearSetReconciliation327.Main.cr23UpStmtAt_crSemAtW_export
-- status  : Proved
-- author  : @djwj233
-- created : 2026-11-21T14:50:42.623335+00:00
-- url     : https://prove2.me/theorems/f19456b5-d2d3-43e7-8d1b-4f5b327f6db1
-- title:
--   The relocated Proposition 2.3 toggle block satisfies the repaired conjunct-6 CR contract `CrSemAtW`
-- statement:
--   For every $1\le t\le N$, every CR sketch $C$, every word-RAM environment $E$ of width $W=\mathrm{cr23Word}\ N$, and every pinned table width $Bw\ge\mathrm{cr23Graph0}\ N$, the relocated Proposition 2.3 toggle block `cr23UpStmtAt` satisfies `CrSemAtW`: for every program $G$ containing the block's compilation at base $b$, every $\delta$ with $\delta+Bw\le 2^W$, every payload base $\beta$ with $\beta+\mathrm{wordsOf}\ W\ (\mathrm{cr23R}\ N\ t)\le 2^W$, and every environment whose table agrees with 2.3's rebased table $\mathrm{cr23DecDetAt}\ N\ t\ C\ \beta$ on the window $[\delta,\delta+Bw)$, the block, started at $b$ with $r_{14}=\delta$, $r_{15}=\beta$ and $r_0=i$, reaches $b+23$ in at most $65536\lg^2(N+2)$ steps, toggles column $i$ of the CR sketch into the payload words $[\beta,\beta+\mathrm{wordsOf}\ W\ (\mathrm{cr23R}\ N\ t))$, and leaves every memory cell outside that window equal to the caller's.
-- source:
--   arXiv:2611.11409 (Liu, Xu, Yang, Zhou, *Linear Set Reconciliation with O(d) Additive Redundancy*), Theorem 6.5 conjunct 6 and Proposition 2.3; the contract shape is `CrSemAt` of Definitions.Def_LinearSetReconciliation327_Main_CR23UpBlk, repaired with the payload-word fit.

import Definitions.Def_LinearSetReconciliation327_Main_CR23UpAt

namespace LinearSetReconciliation327.Main

theorem cr23UpStmtAt_crSemAtW_export (N t : ℕ) (hN : 1 ≤ N) (htN : t ≤ N)
    (C : Fin N → Fin (cr23D N) → Fin (cr23M t))
    (E : RAMEnv) (hEW : E.W = cr23Word N) (Bw : ℕ) (hBw : cr23Graph0 N ≤ Bw) :
    CrSemAtW cr23UpStmtAt E (65536 * lg ((N : ℝ) + 2) ^ 2) Bw N t C := by sorry

end LinearSetReconciliation327.Main
