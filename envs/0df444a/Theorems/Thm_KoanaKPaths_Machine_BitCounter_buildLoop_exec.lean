-- Prove2me | Theorems.Thm_KoanaKPaths_Machine_BitCounter_buildLoop_exec
-- name    : KoanaKPaths.Machine.BitCounter.buildLoop_exec
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T08:12:40.8058+00:00
-- url     : https://prove2.me/theorems/a6dc883f-6eef-4e74-b2bd-b6fcfe59e862
-- title:
--   Convert binary digits to a unary counter by Horner iteration
-- statement:
--   Let $b_1,\ldots,b_r$ be Boolean digits stored most significant first, followed by a marker. Suppose the unary count stack initially contains $m$ markers and then a nonmarker tail, and the temporary stack is empty. The binary-building loop consumes exactly the digits, leaves their delimiter in place, and replaces the unary prefix by $V$ markers, where
--   $$
--   V=\operatorname{foldl}\bigl((q,b)\mapsto2q+b,\ m,\ [b_1,\ldots,b_r]\bigr).
--   $$
--   Every other stack and the input/output state are preserved. Its exact cost satisfies
--   $$
--   C(m,[])=30,\qquad C(m,b::B)=97m+118+2b+C(2m+b,B).
--   $$
--   Here a Boolean is identified with $0$ or $1$. This is the constructive conversion used when a binary index must drive a unary native loop.
-- source:
--   T. Koana, Approximate Counting of k-Paths in O*(2^k) Time, STOC 2027 submission #953, October 2026, §3.2 (printed pp. 8–9 / PDF pp. 9–10) and §4.1 (printed p. 9 / PDF p. 10), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/953.pdf. Native implementation: Solutions/NativeBitCounter.lean, line 37; source snapshot SHA-256 33560a6a9a6de993a978544cc32a39e6071e781a299520a1a3f46cd0e93016e4.

import Definitions.Def_HypergraphUnreliability_FPRAS_Machine
import Definitions.Def_IntMul_SS_Defs1
import Definitions.Def_IntMul_SS_Defs2
import Definitions.Def_KoanaKPaths_ExteriorCoordinates
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

theorem KoanaKPaths.Machine.BitCounter.buildLoop_exec :
∀ (I : List.{0} NLogN.Sym) (s : NLogN.IState KoanaKPaths.Machine.BitCounter.NS) (m : Nat) (bs : List.{0} Bool)
  (bt ct : List.{0} NLogN.Item) (ht : @Ne.{1} NLogN.Cls (NLogN.cls (@List.head?.{0} NLogN.Item ct)) NLogN.Cls.mark)
  (hb :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.BitCounter.NS s KoanaKPaths.Machine.BitCounter.Bits)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.map.{0, 0} Bool NLogN.Item (fun (b : Bool) => NLogN.Item.int (KoanaKPaths.Machine.BitCounter.bitInt b))
          bs)
        (@List.cons.{0} NLogN.Item NLogN.Item.mark bt)))
  (hc :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.BitCounter.NS s KoanaKPaths.Machine.BitCounter.Count)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.replicate.{0} NLogN.Item m NLogN.Item.mark) ct))
  (hx :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.BitCounter.NS s KoanaKPaths.Machine.BitCounter.Tmp)
      (@List.nil.{0} NLogN.Item)),
  @NLogN.IExec KoanaKPaths.Machine.BitCounter.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) I
    (@Fin.elim0.{1}
      (NLogN.IStmt KoanaKPaths.Machine.BitCounter.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    KoanaKPaths.Machine.BitCounter.buildLoop s
    (@NLogN.IState.upd KoanaKPaths.Machine.BitCounter.NS
      (@NLogN.IState.upd KoanaKPaths.Machine.BitCounter.NS s KoanaKPaths.Machine.BitCounter.Bits
        (@List.cons.{0} NLogN.Item NLogN.Item.mark bt))
      KoanaKPaths.Machine.BitCounter.Count
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.replicate.{0} NLogN.Item (KoanaKPaths.Machine.BitCounter.bitValue m bs) NLogN.Item.mark) ct))
    (KoanaKPaths.Machine.BitCounter.buildCost m bs) := by sorry
