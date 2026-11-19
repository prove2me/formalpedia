-- Prove2me | Theorems.Thm_KoanaKPaths_Machine_Trial_trialFold_runs
-- name    : KoanaKPaths.Machine.Trial.trialFold_runs
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T08:15:14.787902+00:00
-- url     : https://prove2.me/theorems/8d73bb22-bec4-4289-9f5b-d36417bb2fea
-- title:
--   Folding trial numerators into an ordered balanced accumulator
-- statement:
--   Let $O$ be a list of trial bit blocks, $k\ge1$, and let $C$ be balanced chunks whose levels are strictly increasing. Assume a ready graph state, the coin stream for $O$, a unary trial counter of length $|O|$, the binary-counter and partials encodings of $C$, and an empty restoration stack. The trial fold consumes those trial streams and replaces the chunk encoding by
--   $$\operatorname{accumulate}\bigl(C,[Z_\omega:\omega\in O]\bigr),$$
--   where $Z_\omega$ is the graph trial numerator. Other state and original tails are restored. Its time is at most $|O|\operatorname{trialFoldBaseCost}(n,k,|A|)+\operatorname{accumulateCharge}(C,[Z_\omega])+30$. This isolates the amortized carry cost from the cost of computing the trials.
-- source:
--   T. Koana, Approximate Counting of k-Paths in O*(2^k) Time, STOC 2027 submission #953, October 2026, §3.2 (printed pp. 8–9 / PDF pp. 9–10) and §4.1 (printed p. 9 / PDF p. 10), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/953.pdf. Native implementation: Solutions/TrialFold.lean, line 32; source snapshot SHA-256 8d4e7e8f58312ce9aeb0b0a73b116c3043e0307d25879ee2988ab65f47fd123e.

import Definitions.Def_HypergraphUnreliability_FPRAS_Machine
import Definitions.Def_IntMul_SS_Defs1
import Definitions.Def_IntMul_SS_Defs2
import Definitions.Def_KoanaKPaths_BitStackAdapter
import Definitions.Def_KoanaKPaths_ExteriorCoordinates
import Definitions.Def_KoanaKPaths_GraphDP
import Definitions.Def_KoanaKPaths_Main_Estimator
import Definitions.Def_KoanaKPaths_Runtime_LiftNative
import Definitions.Def_KoanaKPaths_Runtime_NatParser
import Definitions.Def_KoanaKPaths_Runtime_NativeProgram
import Definitions.Def_KoanaKPaths_Runtime_SubsetArrays
import Definitions.Def_KoanaKPaths_Runtime_TrialIndexing
import Definitions.Def_KoanaKPaths_TapeSampling
import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Size
import Theorems.Thm_KoanaKPaths_Main_graph_dp_sketch
import Theorems.Thm_NLogN_compile_correct
import Theorems.Thm_NLogN_smul_runs
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem KoanaKPaths.Machine.Trial.trialFold_runs :
∀ (I : List.{0} NLogN.Sym) (s : NLogN.IState KoanaKPaths.Machine.Trial.NS) {n k : Nat}
  (arcs : List.{0} (Prod.{0, 0} (Fin n) (Fin n))) (os : List.{0} (Fin (KoanaKPaths.Main.trialBits n k) → Bool))
  (cs : List.{0} KoanaKPaths.Machine.Balanced.Chunk) (tail bt pt : List.{0} NLogN.Item)
  (hk : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) k)
  (hr : @KoanaKPaths.Machine.Trial.Ready n k s arcs)
  (hc :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.TrialCounter)
      (@List.replicate.{0} NLogN.Item (@List.length.{0} (Fin (KoanaKPaths.Main.trialBits n k) → Bool) os)
        NLogN.Item.mark))
  (hCoins :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.Coins)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@KoanaKPaths.Machine.Trial.trialStream n k os) tail))
  (hBits :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Balanced.Bits)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (KoanaKPaths.Machine.Balanced.counterCode (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) cs) bt))
  (hPart :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Balanced.Partials)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.map.{0, 0} Int NLogN.Item NLogN.Item.int
          (@List.map.{0, 0} (Prod.{0, 0} Nat Int) Int (@Prod.snd.{0, 0} Nat Int) cs))
        pt))
  (hRestore :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Balanced.Restore)
      (@List.nil.{0} NLogN.Item))
  (hs :
    @List.Pairwise.{0} KoanaKPaths.Machine.Balanced.Chunk
      (fun (a b : KoanaKPaths.Machine.Balanced.Chunk) =>
        @LT.lt.{0} Nat instLTNat (@Prod.fst.{0, 0} Nat Int a) (@Prod.fst.{0, 0} Nat Int b))
      cs),
  @NLogN.IRuns KoanaKPaths.Machine.Wedge.NS (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) I
    KoanaKPaths.Machine.Wedge.prog KoanaKPaths.Machine.Trial.trialFold s
    (@KoanaKPaths.Machine.Trial.trialFoldState n k s arcs os cs tail bt pt)
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (KoanaKPaths.Machine.Trial.trialFoldBaseCost n k (@List.length.{0} (Prod.{0, 0} (Fin n) (Fin n)) arcs))
          (@List.length.{0} (Fin (KoanaKPaths.Main.trialBits n k) → Bool) os))
        (KoanaKPaths.Machine.Balanced.accumulateCharge cs (@KoanaKPaths.Machine.Trial.numerators n k arcs os)))
      (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))) := by sorry
