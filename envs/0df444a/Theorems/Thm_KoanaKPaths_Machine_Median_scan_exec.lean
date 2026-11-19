-- Prove2me | Theorems.Thm_KoanaKPaths_Machine_Median_scan_exec
-- name    : KoanaKPaths.Machine.Median.scan_exec
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T08:20:27.009513+00:00
-- url     : https://prove2.me/theorems/39ba84c2-9fd3-405c-9a3f-6b973a47aae3
-- title:
--   Counting records at most a midpoint during median search
-- statement:
--   Let the records stack begin with integers $X=(x_1,\ldots,x_m)$ followed by a delimiter, and let a readonly midpoint register contain $q$. The scan consumes these records, places their reversal above the backup stack, and prepends
--   $$\#\{j:x_j\le q\}$$
--   unary markers to the count stack. The record delimiter, original backup and count tails, midpoint, input position, output, and other registers are preserved. Its exact native charge is $\operatorname{scanCost}(q,X)$, obtained by summing integer transfer, readonly comparison, and loop charges for these records. This supports comparison-based median search while accounting for signed bit arithmetic and shared record restoration.
-- source:
--   T. Koana, Approximate Counting of k-Paths in O*(2^k) Time, STOC 2027 submission #953, October 2026, §3.2 (printed pp. 8–9 / PDF pp. 9–10) and §4.1 (printed p. 9 / PDF p. 10), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/953.pdf. Native implementation: Solutions/MedianScan.lean, line 41; source snapshot SHA-256 81ba45c75a5ea64912bf7931abf35338b41d34b1e5120c13625f84f83d468f56.

import Definitions.Def_HypergraphUnreliability_FPRAS_Machine
import Definitions.Def_IntMul_SS_Defs1
import Definitions.Def_IntMul_SS_Defs2
import Definitions.Def_KoanaKPaths_ExteriorCoordinates
import Definitions.Def_KoanaKPaths_Main_Estimator
import Definitions.Def_KoanaKPaths_Runtime_LiftNative
import Definitions.Def_KoanaKPaths_Runtime_NatParser
import Definitions.Def_KoanaKPaths_Runtime_NativeProgram
import Definitions.Def_KoanaKPaths_Runtime_SubsetArrays
import Definitions.Def_KoanaKPaths_Runtime_TrialIndexing
import Mathlib
import Mathlib.Data.Nat.Size
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem KoanaKPaths.Machine.Median.scan_exec :
∀ (I : List.{0} NLogN.Sym) (s : NLogN.IState KoanaKPaths.Machine.Median.NS) (xs : List.{0} Int) (mid : Int)
  (rt mt : List.{0} NLogN.Item) (ht : @Eq.{1} NLogN.Cls (NLogN.cls (@List.head?.{0} NLogN.Item rt)) NLogN.Cls.mark)
  (hr :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Median.NS s KoanaKPaths.Machine.Median.Records)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.map.{0, 0} Int NLogN.Item NLogN.Item.int xs) rt))
  (hm :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Median.NS s KoanaKPaths.Machine.Median.Mid)
      (@List.cons.{0} NLogN.Item (NLogN.Item.int mid) mt)),
  @NLogN.IExec KoanaKPaths.Machine.Median.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) I
    (@Fin.elim0.{1}
      (NLogN.IStmt KoanaKPaths.Machine.Median.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    KoanaKPaths.Machine.Median.scan s
    (@NLogN.IState.upd KoanaKPaths.Machine.Median.NS
      (@NLogN.IState.upd KoanaKPaths.Machine.Median.NS
        (@NLogN.IState.upd KoanaKPaths.Machine.Median.NS s KoanaKPaths.Machine.Median.Records rt)
        KoanaKPaths.Machine.Median.Back
        (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
          (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
          (@List.map.{0, 0} Int NLogN.Item NLogN.Item.int (@List.reverse.{0} Int xs))
          (@NLogN.IState.G KoanaKPaths.Machine.Median.NS s KoanaKPaths.Machine.Median.Back)))
      KoanaKPaths.Machine.Median.Count
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.replicate.{0} NLogN.Item (KoanaKPaths.Machine.Median.countLE mid xs) NLogN.Item.mark)
        (@NLogN.IState.G KoanaKPaths.Machine.Median.NS s KoanaKPaths.Machine.Median.Count)))
    (KoanaKPaths.Machine.Median.scanCost mid xs) := by sorry
