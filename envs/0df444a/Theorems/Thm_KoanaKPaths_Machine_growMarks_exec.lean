-- Prove2me | Theorems.Thm_KoanaKPaths_Machine_growMarks_exec
-- name    : KoanaKPaths.Machine.growMarks_exec
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T08:13:25.208316+00:00
-- url     : https://prove2.me/theorems/03b14f30-4541-49e4-989c-5733afecfc52
-- title:
--   Repeated doubling of a unary count controlled by a depth prefix
-- statement:
--   Let distinct control, count, and temporary native registers contain $d$ control markers, $m$ count markers, and an empty temporary stack. Both marker prefixes are followed by non-marker tails. The growth program consumes the control prefix and replaces the count prefix by
--   $$m2^d\text{ markers}.$$
--   The temporary stack, both tails, input position, output, and other registers are preserved. Its exact charge is the recursion $G(m,0)=30$ and $G(m,d+1)=97m+91+G(2m,d)$. This constructs exponential-sized coordinate counters through repeated doubling while explicitly charging the marker work, rather than treating the resulting unary counter as a free allocation.
-- source:
--   T. Koana, Approximate Counting of k-Paths in O*(2^k) Time, STOC 2027 submission #953, October 2026, §3.2 (printed pp. 8–9 / PDF pp. 9–10) and §4.1 (printed p. 9 / PDF p. 10), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/953.pdf. Native implementation: Solutions/NativePowers.lean, line 16; source snapshot SHA-256 cb8f8408b9ec49b5f39e8c3b32d1bb0187ca79600e8b4f69ec46a44af9b7da21.

import Definitions.Def_HypergraphUnreliability_FPRAS_Machine
import Definitions.Def_IntMul_SS_Defs1
import Definitions.Def_IntMul_SS_Defs2
import Definitions.Def_KoanaKPaths_Runtime_LiftNative
import Definitions.Def_KoanaKPaths_Runtime_NatParser
import Definitions.Def_KoanaKPaths_Runtime_NativeProgram
import Definitions.Def_KoanaKPaths_Runtime_SubsetArrays
import Definitions.Def_KoanaKPaths_Runtime_TrialIndexing
import Mathlib
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem KoanaKPaths.Machine.growMarks_exec :
∀ {S : Nat} (I : List.{0} NLogN.Sym) (control count tmp : Fin S) (hcc : @Ne.{1} (Fin S) control count)
  (hct : @Ne.{1} (Fin S) control tmp) (hcnt : @Ne.{1} (Fin S) count tmp) (s : NLogN.IState S) (d m : Nat)
  (tail tail' : List.{0} NLogN.Item)
  (ht : @Ne.{1} NLogN.Cls (NLogN.cls (@List.head?.{0} NLogN.Item tail)) NLogN.Cls.mark)
  (ht' : @Ne.{1} NLogN.Cls (NLogN.cls (@List.head?.{0} NLogN.Item tail')) NLogN.Cls.mark)
  (hc :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G S s control)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.replicate.{0} NLogN.Item d NLogN.Item.mark) tail))
  (hn :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G S s count)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.replicate.{0} NLogN.Item m NLogN.Item.mark) tail'))
  (hx : @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G S s tmp) (@List.nil.{0} NLogN.Item)),
  @NLogN.IExec S (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) I
    (@Fin.elim0.{1} (NLogN.IStmt S (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@KoanaKPaths.Machine.growMarks S control count tmp) s
    (@NLogN.IState.upd S (@NLogN.IState.upd S s control tail) count
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.replicate.{0} NLogN.Item
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) m
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) d))
          NLogN.Item.mark)
        tail'))
    (KoanaKPaths.Machine.growMarksCost m d) := by sorry
