-- Prove2me | Theorems.Thm_KoanaKPaths_Machine_BitCounter_extractLoop_runs
-- name    : KoanaKPaths.Machine.BitCounter.extractLoop_runs
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T08:13:25.14244+00:00
-- url     : https://prove2.me/theorems/32ffa19e-70e7-4ccf-b60c-8680f82a07f5
-- title:
--   Extracting the binary digits of a natural number on native stacks
-- statement:
--   Let the source register contain a natural number $n$, represented as an integer, and let the readonly ruler register contain $2$. The extraction loop sets the source to zero and prepends the binary digits of $n$ to the bits stack in reverse order relative to the library's least-significant-first digit list:
--   $$\operatorname{Bits}_{\rm after}=\operatorname{reverse}(\operatorname{bitsList}(n))\mathbin{+\!+}\operatorname{Bits}_{\rm before},\qquad t\le528\operatorname{size}(n)+30.$$
--   Digits are stored as native integers $0$ and $1$; zero contributes no digits. All other registers, input position, and output are preserved. This connects binary arithmetic addresses with unary and stack-based lookup controls.
-- source:
--   T. Koana, Approximate Counting of k-Paths in O*(2^k) Time, STOC 2027 submission #953, October 2026, §3.2 (printed pp. 8–9 / PDF pp. 9–10) and §4.1 (printed p. 9 / PDF p. 10), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/953.pdf. Native implementation: Solutions/NativeBitCounter.lean, line 134; source snapshot SHA-256 33560a6a9a6de993a978544cc32a39e6071e781a299520a1a3f46cd0e93016e4.

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

theorem KoanaKPaths.Machine.BitCounter.extractLoop_runs :
∀ (I : List.{0} NLogN.Sym) (n : Nat) (s : NLogN.IState KoanaKPaths.Machine.BitCounter.NS) (st rt : List.{0} NLogN.Item),
  @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.BitCounter.NS s KoanaKPaths.Machine.BitCounter.Source)
      (@List.cons.{0} NLogN.Item (NLogN.Item.int (@Nat.cast.{0} Int instNatCastInt n)) st) →
    @Eq.{1} (List.{0} NLogN.Item)
        (@NLogN.IState.G KoanaKPaths.Machine.BitCounter.NS s KoanaKPaths.Machine.BitCounter.Ruler)
        (@List.cons.{0} NLogN.Item (NLogN.Item.int (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))) rt) →
      @NLogN.IRuns KoanaKPaths.Machine.BitCounter.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) I
        (@Fin.elim0.{1}
          (NLogN.IStmt KoanaKPaths.Machine.BitCounter.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        KoanaKPaths.Machine.BitCounter.extractLoop s
        (@NLogN.IState.upd KoanaKPaths.Machine.BitCounter.NS
          (@NLogN.IState.upd KoanaKPaths.Machine.BitCounter.NS s KoanaKPaths.Machine.BitCounter.Source
            (@List.cons.{0} NLogN.Item (NLogN.Item.int (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0)))) st))
          KoanaKPaths.Machine.BitCounter.Bits
          (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
            (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
            (@List.map.{0, 0} Bool NLogN.Item
              (fun (b : Bool) => NLogN.Item.int (KoanaKPaths.Machine.BitCounter.bitInt b))
              (@List.reverse.{0} Bool (Nat.bits n)))
            (@NLogN.IState.G KoanaKPaths.Machine.BitCounter.NS s KoanaKPaths.Machine.BitCounter.Bits)))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 528) (instOfNatNat (nat_lit 528))) (Nat.size n))
          (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))) := by sorry
