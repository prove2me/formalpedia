-- Prove2me | Theorems.Thm_LinearSetReconciliation327_Main_CRS_hdecW
-- name    : LinearSetReconciliation327.Main.CRS.hdecW
-- status  : Proved
-- author  : @djwj233
-- created : 2026-11-23T11:35:51.005157+00:00
-- url     : https://prove2.me/theorems/1e5ee59c-705d-4a00-a8f0-c838862de924
-- title:
--   Proposition 2.3's decoder from a finite zero tail (the window-pin hypothesis of Theorem 6.5)
-- statement:
--   Let $\mathrm{progDec}$ be the decoder program of Proposition 2.3 for the parity-check matrix $CR_{N,t}$ built from a layered expander $C$ with $16\varepsilon \le 1$, let $W = \mathrm{cr23Word}\,N$ be the word width and $M = \mathrm{cr23R}\,N\,t$ the number of check rows, and let $y$ be the packed sketch of a vector $x$ with $|\mathrm{supp}\,x| \le t$.
--
--   Write $Z = \mathrm{decOutBase}\,N\,t$ for the base of the decoder's output window.  The theorem states: from **any** machine state $s$ with $s.\mathrm{pc} = 0$ whose memory holds the payload on the finite window $[0, \mathrm{wordsOf}\,W\,M)$ and is zero on $[\mathrm{wordsOf}\,W\,M,\ Z)$ — with the memory at every address $\ge Z$ left **completely arbitrary** — the decoder halts within its published budget $\mathrm{decStmtCost}\,N\,t + 1$, outputs the support of $x$ in its output window and leaves $s'.r_0 = Z$.
--
--   The bound is exact and is the round's key quantity: the published proof of Proposition 2.3 reads the zero tail only in its prologue, at the three sites $\mathrm{decTagBase}\,N\,t + v$ and $\mathrm{decParBase}\,N\,t + v$ with $v < 2^{\mathrm{cr23Lb}\,N + 1}$, so the largest address read is $Z - 1$; in closed form $$Z \;=\; M + 3N(W - 1024) + N + 4t + 37 + 2^{\mathrm{cr23Lb}\,N + 2}.$$
--
--   This is precisely the fifth hypothesis of the window-pin repair of Theorem 6.5's $cr$ field: the published Proposition 2.3 needs an *infinite* tail of zeros, which no finite program can restore, and the theorem shows that a finite tail of length $Z$ suffices, with garbage above it.
-- source:
--   arXiv:2611.11409 (Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, *Linear Set Reconciliation with O(d) Additive Redundancy*), Proposition 2.3 and Theorem 6.5; the finite-window entry predicate is the project's `CrStageInWz20261123`, the engine is the project's `CR23DecExitWz20261123` (a re-run of the published `CR23DecExit20261122` with the zero hypothesis restricted to `[wordsOf W M, Z)`).

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_CR23DecExitWz20261123
import Definitions.Def_LinearSetReconciliation327_Main_CrStageInWz20261123

namespace LinearSetReconciliation327.Main.CRS

open LinearSetReconciliation327.Main

/-- **`hdecW`**: Proposition 2.3's decoder from the finite window pin (zeros only below
`decZeroBound N t`, memory at `>= Z` arbitrary). -/
theorem hdecW (N t : ℕ) (hN : 1 ≤ N) (ht : 1 ≤ t) (htN : t ≤ N)
    (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (x : Fin N → ZMod 2) (eps : ℝ)
    (hexp : IsLayeredExpander C (2 * t) eps) (heps : 16 * eps ≤ 1)
    (hsup : (cr23Supp x).card ≤ t) (Z : ℕ) (hZ : decZeroBound N t ≤ Z)
    (ab al bb bl ob : ℕ) (Lx : List ℕ) (st : RAMState) (hpc : st.pc = 0)
    (hIn : CrStageInWz (detEnv (cr23Word N) (cr23DecDet N t C)) (cr23R N t) Z
      (cr23Sketch N t C x) ab al bb bl ob Lx st) :
    ∃ s' : RAMState,
      HaltsWithin progDec (detEnv (cr23Word N) (cr23DecDet N t C))
        ((decStmtCost N t : ℝ) + 1) st s' ∧
        OutputsSupport s' x ∧ s'.regs r0 = decOutBase N t := by
  sorry

end LinearSetReconciliation327.Main.CRS
