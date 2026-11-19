-- Prove2me | Theorems.Thm_KoanaKPaths_Machine_Native_invariant_loop
-- name    : KoanaKPaths.Machine.Native.invariant_loop
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T08:11:30.950814+00:00
-- url     : https://prove2.me/theorems/0b097e88-f6fb-4fac-a934-c900ee2e771e
-- title:
--   Lift a bounded loop invariant to a native execution bound
-- statement:
--   Consider a native while-loop with $L$ counter markers followed by a nonmarker tail. Let $\mathcal I(j,s)$ be a state invariant describing completion of $j$ iterations, including that the remaining loop counter has $L-j$ markers. Suppose that whenever $j<L$ and $\mathcal I(j,s)$ holds, the body runs within $C$ charged steps to some state satisfying $\mathcal I(j+1,\cdot)$. From any state satisfying $\mathcal I(0,\cdot)$, the loop therefore reaches a state satisfying $\mathcal I(L,\cdot)$ within
--   $$
--   (C+30)L+30.
--   $$
--   The statement applies to arbitrary input and procedure environments. Consumption of the counter is part of the assumed invariant transition. This rule packages the loop reasoning used throughout array, graph and sampling programs.
-- source:
--   T. Koana, Approximate Counting of k-Paths in O*(2^k) Time, STOC 2027 submission #953, October 2026, §3.2 (printed pp. 8–9 / PDF pp. 9–10) and §4.1 (printed p. 9 / PDF p. 10), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/953.pdf. Native implementation: Solutions/NativeInvariantLoop.lean, line 10; source snapshot SHA-256 56adfecc773272e565ae9a954e2bf78aa57c82ab1df0daceb9a834f3fa2bc098.

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

theorem KoanaKPaths.Machine.Native.invariant_loop :
∀ {S P : Nat} (I : List.{0} NLogN.Sym) (prog : Fin P → NLogN.IStmt S P) (counter : Fin S) (body : NLogN.IStmt S P)
  (Inv : Nat → NLogN.IState S → Prop) (L C : Nat) (tail : List.{0} NLogN.Item)
  (ht : @Ne.{1} NLogN.Cls (NLogN.cls (@List.head?.{0} NLogN.Item tail)) NLogN.Cls.mark)
  (hcounter :
    ∀ (i : Nat),
      @LE.le.{0} Nat instLENat i L →
        ∀ (s : NLogN.IState S),
          Inv i s →
            @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G S s counter)
              (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
                (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
                (@List.replicate.{0} NLogN.Item (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) L i)
                  NLogN.Item.mark)
                tail))
  (hstep :
    ∀ (i : Nat),
      @LT.lt.{0} Nat instLTNat i L →
        ∀ (s : NLogN.IState S),
          Inv i s →
            @Exists.{1} (NLogN.IState S) fun (s' : NLogN.IState S) =>
              And (@NLogN.IRuns S P I prog body s s' C)
                (Inv
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  s'))
  (s : NLogN.IState S) (hs : Inv (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) s),
  @Exists.{1} (NLogN.IState S) fun (s' : NLogN.IState S) =>
    And
      (@NLogN.IRuns S P I prog
        (@NLogN.IStmt.loop S P counter
          (fun (c : NLogN.Cls) =>
            @Decidable.decide (@Eq.{1} NLogN.Cls c NLogN.Cls.mark) (NLogN.instDecidableEqCls c NLogN.Cls.mark))
          body)
        s s'
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) C
              (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))))
            L)
          (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))))
      (Inv L s') := by sorry
