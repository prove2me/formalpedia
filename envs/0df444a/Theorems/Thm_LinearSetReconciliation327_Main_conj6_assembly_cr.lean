-- Prove2me | Theorems.Thm_LinearSetReconciliation327_Main_conj6_assembly_cr
-- name    : LinearSetReconciliation327.Main.conj6_assembly_cr
-- status  : Proved
-- author  : @djwj233
-- created : 2026-11-21T15:34:23.717901+00:00
-- url     : https://prove2.me/theorems/4b515337-dfb0-42ae-bd0b-699a44ac0e36
-- title:
--   Theorem 6.5, conjunct 6: the composite toggle reaches the packed payload in $7 + (8\ell + \ell T_u) + 2 + 3 + 65536\lg^2(N+2)$ steps
-- statement:
--   This is **conjunct 6** of Theorem 6.5 --- the *toggle* conjunct --- for the composite programme of the linear-set-reconciliation scheme of arXiv:2611.11409.
--
--   Fix $1 \le N$, $t \le N$, a linear map $C : (\mathbb{Z}/2)^N \to (\mathbb{Z}/2)^{\mathrm{cr23D}\ N}$, a word-RAM environment $E$ of width $W = \mathrm{cr23Word}\ N$, a block width $W_d \ge 2$, $\ell$ child blocks with payload lengths $f : \mathrm{Fin}\,\ell \to \mathbb{N}$ (word-padded: $W \cdot \mathrm{wordsOf}\ W\ (f\,s) = f\,s$) and sketches $H_s : (\mathbb{Z}/2)^N \to (\mathbb{Z}/2)^{f\,s}$, and a payload base $\mathrm{Rpad} \ge \mathrm{cr23Graph0}\ N$ for the CR block.  The environment's deterministic table is the composite one:
--
--   $$ \mathrm{det} = \mathrm{compUpDetB}\ W_d\ \mathrm{Rpad}\ dt\ (\mathrm{cr23DecDetAt}\ N\ t\ C\ (\mathrm{blkTotal}\ W\ f))\ (\mathrm{blkOff}\ W\ f)\ (\mathrm{blkTotal}\ W\ f), $$
--
--   i.e. a metadata block holding $\ell+1$, $2^{W_d}$ and the address of the payload-base table, then the $\ell$ child blocks, then the CR block whose table is Proposition 2.3's rebased table together with the payload bases $\beta_s = \mathrm{blkOff}\ W\ f\ s$.
--
--   **Hypothesis (Theorem 5.1's obligation).**  Each child block satisfies the run contract $\mathrm{UpBlkSemC}\ \mathit{Sup}\ E\ T_u\ 2^{W_d}\ (f\,s)\ (H_s)$ at the pinned block width: for every program containing the block's compilation at a base $b$, every $\delta$ with $\delta + 2^{W_d} \le 2^W$, every payload base $\beta$ with $\beta + \mathrm{wordsOf}\ W\ (f\,s) \le 2^W$, and every environment whose table agrees with $dt_s$ on $[\delta,\delta+2^{W_d})$, the block --- started with $r_{14}=\delta$, $r_{15}=\beta$, $r_0 = i$ --- toggles $H_s(e_i)$ into the payload at $\beta$ within $T_u$ steps, returns to $b + \mathrm{Sup.len}$, preserves $r_0,\dots,r_4$, and touches no memory cell outside the payload window.  Crucially the **CR block is not a hypothesis**: it is discharged from Proposition 2.3's relocated toggle (`cr23UpStmtAt_crSemAtW`), at cost $65536\lg^2(N+2)$.
--
--   **Conclusion.**  Under the arithmetic fits that make the layout non-overlapping ($R\mathrm{pad} \le 2^{W_d}$, $2^{W_d} < 2^W$, $(\ell+1)2^{W_d} + \mathrm{Rpad} \le 2^W$, $\mathrm{blkTotal}\ W\ f + \mathrm{wordsOf}\ W\ (\mathrm{cr23R}\ N\ t) \le 2^W$, …), for every payload $y$ of $W \cdot \mathrm{blkTotal}\ W\ f + \mathrm{cr23R}\ N\ t$ bits and every coordinate $i$, the composite programme `progUpOfProB Sup cr23UpStmtAt` admits a run of length at most
--
--   $$ 7 + (8\ell + \ell T_u) + 2 + 3 + 65536\lg^2(N+2) $$
--
--   steps from the initialised state `initState (packMem E.W y) i.val 0 0` to a state whose memory is the packed payload of
--
--   $$ y + \mathrm{compH}\ W\ f\ (\mathrm{cr23R}\ N\ t)\ H\ (\mathrm{cr23Sketch}\ N\ t\ C)\ (e_i), $$
--
--   i.e. the composite sketch $\bigl(H_0(e_i),\dots,H_{\ell-1}(e_i), \mathrm{CR}(e_i)\bigr)$ is toggled into the packed payload.  The bound is the paper's: $7$ for the prologue, $8\ell + \ell T_u$ for the $\ell$ child blocks, $2$ for the failing loop test and the jump, $3$ for the dispatch to the CR block, and $65536\lg^2(N+2)$ for the CR block.
--
--   **Formalization Note.**  The contract is stated at the *pinned* block width $2^{W_d}$ and carries the payload-word fit $\beta + \mathrm{wordsOf}\ W\ M \le 2^W$: the published shape without the fit is falsifiable, since `iTbl` reduces a table entry modulo $2^W$.  The CR premise of the earlier assembly is not a hypothesis here --- it is proved, axiom-clean, inside the imported bundle.
-- source:
--   arXiv:2611.11409 (Liu, Xu, Yang, Zhou, *Linear Set Reconciliation with O(d) Additive Redundancy*), §6.1, Theorem 6.5, conjunct 6 (with Proposition 2.3 for the CR block and Theorem 5.1 for the per-block contract).

import Definitions.Def_LinearSetReconciliation327_Main_Conj6CR

namespace LinearSetReconciliation327.Main

theorem conj6_assembly_cr
    (Sup : Stmt) (E : RAMEnv) {l N t Wd Rpad : ℕ} {f : Fin l → ℕ}
    {dt : Fin l → ℕ → ℕ}
    {Hs : (s : Fin l) → (Fin N → ZMod 2) →ₗ[ZMod 2] (Fin (f s) → ZMod 2)}
    {C : Fin N → Fin (cr23D N) → Fin (cr23M t)}
    {Tu : ℝ} (hTu : 0 ≤ Tu)
    (hW : 0 < E.W) (hW1 : 1 < 2 ^ E.W) (hWd1 : 1 ≤ Wd) (hWd2 : 2 ≤ Wd)
    (hpad : ∀ s : Fin l, E.W * wordsOf E.W (f s) = f s)
    (hUp : UpChildSemC Sup E Tu (2 ^ Wd) f Hs)
    (hE : E.det = compUpDetB Wd Rpad dt (cr23DecDetAt N t C (blkTotal E.W f))
      (fun s => blkOff E.W f s.val) (blkTotal E.W f))
    (hN : 1 ≤ N) (htN : t ≤ N) (hEW : E.W = cr23Word N) (hBw : cr23Graph0 N ≤ Rpad)
    (hWdW : 2 ^ Wd < 2 ^ E.W) (hlW : l + 1 < 2 ^ E.W)
    (hRpad : 0 < Rpad) (hRfit : Rpad ≤ 2 ^ Wd) (hpayfit : Rpad + l ≤ 2 ^ Wd)
    (hlWd : (l + 1) * 2 ^ Wd < 2 ^ E.W)
    (hcrfit : (l + 1) * 2 ^ Wd + Rpad ≤ 2 ^ E.W)
    (hpaylt : compPayBase l Wd Rpad + l ≤ 2 ^ E.W)
    (hbtlt : blkTotal E.W f < 2 ^ E.W)
    (hbtfit : blkTotal E.W f + wordsOf E.W (cr23R N t) ≤ 2 ^ E.W)
    (y : Fin (E.W * blkTotal E.W f + (cr23R N t)) → ZMod 2) (i : Fin N) :
    ∃ s' : RAMState,
      HaltsWithin (progUpOfProB Sup cr23UpStmtAt) E
        (7 + (8 * (l : ℝ) + (l : ℝ) * Tu) + 2 + 3 + (65536 * lg ((N : ℝ) + 2) ^ 2))
        (initState (packMem E.W y) i.val 0 0) s' ∧
      (∀ addr < wordsOf E.W (E.W * blkTotal E.W f + (cr23R N t)),
        s'.mem addr
          = packMem E.W (y + compH E.W hW f (cr23R N t) Hs (cr23Sketch N t C) (Pi.single i 1)) addr) := by sorry

end LinearSetReconciliation327.Main
