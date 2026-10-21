-- Prove2me | Theorems.Thm_NLogN_KFV_body18_runs
-- name    : NLogN.KFV.body18_runs
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-20T19:20:56.753544+00:00
-- url     : https://prove2.me/theorems/16d24e81-2616-4ea4-8652-5e66ca376038
-- title:
--   The body of the uniform Proposition 18 program (round six, `body18_runs`)
-- statement:
--   **The body of the uniform Proposition 18 program.**
--
--   The following holds (Lean statement, in the scope of module `Solutions.KFV52Body`):
--
--   ```lean
--   theorem NLogN.KFV.body18_runs {su td : IStmt HS Pp} {e14 eSw pM : Fin Pp} {Kc : ℝ}
--       (HSw : SwOK I iprog eSw dW18 Kc) (hKc : 0 ≤ Kc)
--       {M : MulSpec} (hM : MulOK I iprog pM M) (hdom : ∀ x y, M.dom x y)
--       (p ℓ K : ℕ) (ts : List ℕ) [NeZero ts.length] (hK : 0 < K) (hℓ : 2 ≤ ℓ) (hq1 : 1 ≤ qq ℓ K)
--       {cCh U B BK φ cs ct : ℕ}
--       (HC : ChunkU ts.length ℓ K (long18 ℓ ts) I iprog e14 hK (by omega) p (p + 2)
--         (n18 ℓ K ts + ℓ + 8) cCh)
--       (hB : n18 ℓ K ts + ℓ + 5 ≤ B) (hNB : ts.length * qq ℓ K + ts.length + 1 ≤ B)
--       (hWB : p + 2 ≤ B) (hbL : bL ts.length ℓ K (long18 ℓ ts) ≤ B)
--       (hU : TwB ts.length ℓ K (long18 ℓ ts) U)
--       (hΦ : ∀ x y : ℤ, zsz x ≤ kb p ℓ * 2 ^ ℓ + 2 → zsz y ≤ kb p ℓ * 2 ^ ℓ + 2 → M.Φ x y ≤ φ)
--       (hBK : 2 * (kb p ℓ * 2 ^ ℓ) + p + n18 ℓ K ts + ℓ + 8 ≤ BK)
--       (hB2 : p + 2 + n18 ℓ K ts + ℓ + 4 ≤ B)
--       (s : IState HS) (f : Fin HS → List ℤ)
--       (Hsu : IRuns I iprog su (encK s f) (encK (encK s (regs18 p ℓ K ts)) (o0 (f 0))) cs)
--       {zf zg : List GI} (l : List ℤ) {xf xg : List (Fin (2 ^ ℓ) → ℂ)}
--       (Htd : ∀ zh : List GI, IRuns I iprog td (encK (encK s (regs18 p ℓ K ts)) (o0 (gflat zh ++ l)))
--         (encK s (Function.update f 0 (gflat zh ++ l))) ct)
--       (h0 : f 0 = gflat zf ++ (gflat zg ++ l))
--       (hxf : RecRep (2 ^ ℓ) p zf xf) (hxg : RecRep (2 ^ ℓ) p zg xg)
--       (hlf : xf.length = 2 ^ n18 ℓ K ts) (hlg : xg.length = 2 ^ n18 ℓ K ts)
--       (hbf : GB (p + 2) zf) (hbg : GB (p + 2) zg) (hdf : Disk xf) (hdg : Disk xg) :
--       let Lin : List (Fin (2 ^ ℓ) → ℂ) → List (Fin (2 ^ ℓ) → ℂ) :=
--         pull (binSh (n18 ℓ K ts)) (binSh (n18 ℓ K ts)) (relabel (initL ts.length ℓ (long18 ℓ ts))
--           (tgtL ts.length ℓ K (long18 ℓ ts))) 0
--       let Lout : List (Fin (2 ^ ℓ) → ℂ) → List (Fin (2 ^ ℓ) → ℂ) :=
--         pull (binSh (n18 ℓ K ts)) (binSh (n18 ℓ K ts)) (relabel (tgtL ts.length ℓ K (long18 ℓ ts))
--           (initL ts.length ℓ (long18 ℓ ts))) 0
--       let F := procQc (r := 2 ^ ℓ) p (paperLayout ts.length ℓ K (long18 ℓ ts) hK (by omega)) ℓ
--         (partAxes (al ts.length ℓ (long18 ℓ ts))) (paperSel ts.length ℓ K (long18 ℓ ts) hK (by omega)) ℓ
--       let G := procQIc (r := 2 ^ ℓ) p (paperLayout ts.length ℓ K (long18 ℓ ts) hK (by omega)) ℓ
--         (partAxes (al ts.length ℓ (long18 ℓ ts))) (paperSel ts.length ℓ K (long18 ℓ ts) hK (by omega)) ℓ
--       ∃ zh : List GI,
--         RecRep (2 ^ ℓ) p zh ((Lout (G (List.zipWith (ppq (2 ^ ℓ) p) (F (Lin xf)) (F (Lin xg))))).map
--           fun x => ((2 : ℂ) ^ n18 ℓ K ts) • x) ∧
--         (Lout (G (List.zipWith (ppq (2 ^ ℓ) p) (F (Lin xf)) (F (Lin xg))))).length = 2 ^ n18 ℓ K ts ∧
--         IRuns I iprog (body18 su td e14 eSw pM) (encK s f)
--           (encK s (Function.update f 0 (gflat zh ++ l)))
--           (cs + (cCore18 (cLayIn ts.length ℓ K (long18 ℓ ts) Kc (n18 ℓ K ts) (p + 2) B +
--               NLogN.KFV.cFwd ts.length ℓ K (long18 ℓ ts) (p + 2) B cCh U)
--             (cOpp ts.length ℓ K (long18 ℓ ts) (p + 2) B cCh U +
--               cLayOut ts.length ℓ K (long18 ℓ ts) Kc (n18 ℓ K ts) (p + 2) B)
--             (n18 ℓ K ts) ℓ p B BK φ + ct))
--   ```
--
--   **Context.** KFV §52: the body of the uniform Proposition 18 program
--
--   `body18 su td e14 eSw pM = su ; core18 (fwd18 e14 eSw) (opp18 e14 eSw) pM ; td`.
--
--   **`body18_runs`**: from the descriptor `desc18 p ℓ K ts` on `dS18` and `zf` over `zg` on stack `0`
--   (all else empty, base `s` arbitrary), the body leaves `zh` (over the rest `l`) on stack `0` and
--   restores everything else; `zh` represents
--   `(Lout ∘ procQIc) (zipWith ppq ((procQc ∘ Lin) xf) ((procQc ∘ Lin) xg))` scaled by `2^n`.
--
--   **Formalization Note.** Part of the Lean formalization of the round-six κ-improvement (integer-multiplication-kappa campaign, target `IntMul.Kappa.jain_round6_framework`). The statement is copied verbatim from the Lean development; the platform node carries the same declaration name. Definitions it mentions live in the `IntMul_Kappa_R6_Defs*` bundles (on top of the published κ bundles `IntMul_Kappa_K_Defs*`).
-- source:
--   S. Jain, round-six networks for the integer-multiplication κ-improvement campaign (https://github.com/Swapnil-jain/integer-mult-kappa, commit 5868dc7) and D. Colkitt, integer-mult-bounds (https://github.com/CrocSwap/integer-mult-bounds); target `IntMul.Kappa.jain_round6_framework`. Lean declaration `NLogN.KFV.body18_runs`, Solutions/KFV52Body.lean (lines 37–99) of the round-six development.

-- Round-six κ development (integer-multiplication-kappa), generated by skeleton subtraction.

import Definitions.Def_IntMul_Kappa_K_Defs33
import Definitions.Def_IntMul_Kappa_R6_Defs1
import Mathlib
import Definitions.Def_IntMul_HvdH_M_Defs8
import Definitions.Def_IntMul_MultitapeModel
import Definitions.Def_IntMul_HvdH_Numeric
import Definitions.Def_IntMul_HvdH_ExpApprox
import Definitions.Def_IntMul_HvdH_RealExp
import Definitions.Def_IntMul_HvdH_Twiddle
import Definitions.Def_IntMul_HvdH_MachineRef

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

open NLogN NLogN.KFV
open IntMul NLogN.RS NLogN.KIL NLogN.KFD NLogN.KFB NLogN.KFH NLogN.KFC NLogN.KFT Synth AModel AModelL12 GlueLayout GlueP14 GlueError
variable {Pp : ℕ} {I : List Sym} {iprog : Fin Pp → IStmt HS Pp}

theorem NLogN.KFV.body18_runs {su td : IStmt HS Pp} {e14 eSw pM : Fin Pp} {Kc : ℝ}
    (HSw : SwOK I iprog eSw dW18 Kc) (hKc : 0 ≤ Kc)
    {M : MulSpec} (hM : MulOK I iprog pM M) (hdom : ∀ x y, M.dom x y)
    (p ℓ K : ℕ) (ts : List ℕ) [NeZero ts.length] (hK : 0 < K) (hℓ : 2 ≤ ℓ) (hq1 : 1 ≤ qq ℓ K)
    {cCh U B BK φ cs ct : ℕ}
    (HC : ChunkU ts.length ℓ K (long18 ℓ ts) I iprog e14 hK (by omega) p (p + 2)
      (n18 ℓ K ts + ℓ + 8) cCh)
    (hB : n18 ℓ K ts + ℓ + 5 ≤ B) (hNB : ts.length * qq ℓ K + ts.length + 1 ≤ B)
    (hWB : p + 2 ≤ B) (hbL : bL ts.length ℓ K (long18 ℓ ts) ≤ B)
    (hU : TwB ts.length ℓ K (long18 ℓ ts) U)
    (hΦ : ∀ x y : ℤ, zsz x ≤ kb p ℓ * 2 ^ ℓ + 2 → zsz y ≤ kb p ℓ * 2 ^ ℓ + 2 → M.Φ x y ≤ φ)
    (hBK : 2 * (kb p ℓ * 2 ^ ℓ) + p + n18 ℓ K ts + ℓ + 8 ≤ BK)
    (hB2 : p + 2 + n18 ℓ K ts + ℓ + 4 ≤ B)
    (s : IState HS) (f : Fin HS → List ℤ)
    (Hsu : IRuns I iprog su (encK s f) (encK (encK s (regs18 p ℓ K ts)) (o0 (f 0))) cs)
    {zf zg : List GI} (l : List ℤ) {xf xg : List (Fin (2 ^ ℓ) → ℂ)}
    (Htd : ∀ zh : List GI, IRuns I iprog td (encK (encK s (regs18 p ℓ K ts)) (o0 (gflat zh ++ l)))
      (encK s (Function.update f 0 (gflat zh ++ l))) ct)
    (h0 : f 0 = gflat zf ++ (gflat zg ++ l))
    (hxf : RecRep (2 ^ ℓ) p zf xf) (hxg : RecRep (2 ^ ℓ) p zg xg)
    (hlf : xf.length = 2 ^ n18 ℓ K ts) (hlg : xg.length = 2 ^ n18 ℓ K ts)
    (hbf : GB (p + 2) zf) (hbg : GB (p + 2) zg) (hdf : Disk xf) (hdg : Disk xg) :
    let Lin : List (Fin (2 ^ ℓ) → ℂ) → List (Fin (2 ^ ℓ) → ℂ) :=
      pull (binSh (n18 ℓ K ts)) (binSh (n18 ℓ K ts)) (relabel (initL ts.length ℓ (long18 ℓ ts))
        (tgtL ts.length ℓ K (long18 ℓ ts))) 0
    let Lout : List (Fin (2 ^ ℓ) → ℂ) → List (Fin (2 ^ ℓ) → ℂ) :=
      pull (binSh (n18 ℓ K ts)) (binSh (n18 ℓ K ts)) (relabel (tgtL ts.length ℓ K (long18 ℓ ts))
        (initL ts.length ℓ (long18 ℓ ts))) 0
    let F := procQc (r := 2 ^ ℓ) p (paperLayout ts.length ℓ K (long18 ℓ ts) hK (by omega)) ℓ
      (partAxes (al ts.length ℓ (long18 ℓ ts))) (paperSel ts.length ℓ K (long18 ℓ ts) hK (by omega)) ℓ
    let G := procQIc (r := 2 ^ ℓ) p (paperLayout ts.length ℓ K (long18 ℓ ts) hK (by omega)) ℓ
      (partAxes (al ts.length ℓ (long18 ℓ ts))) (paperSel ts.length ℓ K (long18 ℓ ts) hK (by omega)) ℓ
    ∃ zh : List GI,
      RecRep (2 ^ ℓ) p zh ((Lout (G (List.zipWith (ppq (2 ^ ℓ) p) (F (Lin xf)) (F (Lin xg))))).map
        fun x => ((2 : ℂ) ^ n18 ℓ K ts) • x) ∧
      (Lout (G (List.zipWith (ppq (2 ^ ℓ) p) (F (Lin xf)) (F (Lin xg))))).length = 2 ^ n18 ℓ K ts ∧
      IRuns I iprog (body18 su td e14 eSw pM) (encK s f)
        (encK s (Function.update f 0 (gflat zh ++ l)))
        (cs + (cCore18 (cLayIn ts.length ℓ K (long18 ℓ ts) Kc (n18 ℓ K ts) (p + 2) B +
            NLogN.KFV.cFwd ts.length ℓ K (long18 ℓ ts) (p + 2) B cCh U)
          (cOpp ts.length ℓ K (long18 ℓ ts) (p + 2) B cCh U +
            cLayOut ts.length ℓ K (long18 ℓ ts) Kc (n18 ℓ K ts) (p + 2) B)
          (n18 ℓ K ts) ℓ p B BK φ + ct)) := by sorry
