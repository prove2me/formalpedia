-- Prove2me | Theorems.Thm_LinearSetReconciliation327_Main_cr23_decoding
-- name    : LinearSetReconciliation327.Main.cr23_decoding
-- status  : Proved
-- author  : @djwj233
-- created : 2026-11-22T06:47:27.629365+00:00
-- url     : https://prove2.me/theorems/fe66f7e6-81d5-4896-bfb2-8afc6ae60102
-- title:
--   Proposition 2.3's concrete decoding run at the decoder program `progDec`
-- statement:
--   Let $N\ge 1$, $1\le t\le N$, let $C$ be the $N\times D\times M$ CR23 sketch with $D=1024\,\lceil\log_2(N+1)\rceil$ and $M=4096\,t$, and let $\varepsilon\in\mathbb{R}$ be such that $C$ is a layered expander for $2t$ labels with error $\varepsilon$ and $16\varepsilon\le 1$.  Then for **every** $x\in\mathbb{F}_2^N$ whose Hamming weight is at most $t$, the decoder program $\mathrm{progDec}$ of Proposition 2.3, started at address $0$ from the initial state whose payload words are the packed sketch $y=\mathrm{cr23Sketch}\ N\ t\ C\ x$, halts within $$2^{85}\cdot\max\bigl(1,\; t\cdot\lg(t+2)\cdot\lg(N+2)\bigr)$$ word-RAM steps and outputs the support of $x$: the duplicate-free list it leaves in its output window is exactly $\{i : x_i = 1\}$.
-- source:
--   arXiv:2611.11409 (Liu, Xu, Yang, Zhou, *Linear Set Reconciliation with O(d) Additive Redundancy*), §2.3, Proposition 2.3, second conjunct (the decoding guarantee). Extracted by skeleton subtraction from the accepted development `Solutions/Sol_proposition_2_3.lean` (`theorem cr23_decoding`, line 14635), copied byte-identically.

import Definitions.Def_LinearSetReconciliation327_Main_CR23Dec
import Definitions.Def_LinearSetReconciliation327_Main_CR23Run20261122

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_Basic
import Definitions.Def_LinearSetReconciliation327_Main_Framework
import Definitions.Def_LinearSetReconciliation327_Main_HintSketch
import Definitions.Def_LinearSetReconciliation327_Main_Pinsketch
import Definitions.Def_LinearSetReconciliation327_Main_TopLevel
import Definitions.Def_LinearSetReconciliation327_Main_WordRAM
import Definitions.Def_LinearSetReconciliation327_Main_DecoderModel
import Definitions.Def_LinearSetReconciliation327_Main_CR23
import Definitions.Def_LinearSetReconciliation327_Main_CR23Dec
import Definitions.Def_LinearSetReconciliation327_Main_CR23Run20261122

namespace LinearSetReconciliation327.Main

theorem cr23_decoding (N t : ℕ) (hN : 1 ≤ N) (ht : 1 ≤ t) (htN : t ≤ N)
    (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (eps : ℝ)
    (hexp : IsLayeredExpander C (2 * t) eps) (heps : 16 * eps ≤ 1) :
    ∀ x : Fin N → ZMod 2, (Finset.univ.filter fun i => x i = 1).card ≤ t →
      ∃ s' : RAMState,
        HaltsWithin progDec (detEnv (cr23Word N) (cr23DecDet N t C))
          ((2 : ℝ) ^ 85 * max 1 ((t : ℝ) * lg ((t : ℝ) + 2) * lg ((N : ℝ) + 2)))
          (decoderStart (cr23Word N) (cr23Sketch N t C x) []) s' ∧
          OutputsSupport s' x := by sorry

end LinearSetReconciliation327.Main
