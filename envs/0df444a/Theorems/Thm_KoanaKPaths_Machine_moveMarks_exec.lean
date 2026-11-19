-- Prove2me | Theorems.Thm_KoanaKPaths_Machine_moveMarks_exec
-- name    : KoanaKPaths.Machine.moveMarks_exec
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T08:18:22.456846+00:00
-- url     : https://prove2.me/theorems/508caa6b-6a93-47c9-8a86-81388c05af42
-- title:
--   Moving a delimited unary marker counter with exact native cost
-- statement:
--   Let distinct native registers contain a source prefix of $m$ unary markers above a non-marker tail and an arbitrary destination stack. The marker-moving loop consumes exactly that prefix and prepends it to the destination:
--   $$\operatorname{Src}=\#^mT\longmapsto T,\qquad\operatorname{Dst}\longmapsto\#^m\operatorname{Dst},\qquad t=32m+30.$$
--   Every other register, input position, output, and existing stack tail is preserved. The theorem holds for all natural $m$, including zero, and makes no assumption about the destination tail. This basic frame-aware counter transport is used in count copying, doubling, and the finite loops that traverse coordinate arrays.
-- source:
--   T. Koana, Approximate Counting of k-Paths in O*(2^k) Time, STOC 2027 submission #953, October 2026, §3.2 (printed pp. 8–9 / PDF pp. 9–10) and §4.1 (printed p. 9 / PDF p. 10), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/953.pdf. Native implementation: Solutions/NativeMarks.lean, line 28; source snapshot SHA-256 f11453357c827c9f073c70c6f785ed2027d21b6c69f3c4a5894d8ecea7743cbb.

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

theorem KoanaKPaths.Machine.moveMarks_exec :
∀ {S : Nat} (I : List.{0} NLogN.Sym) (src dst : Fin S) (hne : @Ne.{1} (Fin S) src dst) (s : NLogN.IState S) (m : Nat)
  (tail : List.{0} NLogN.Item) (ht : @Ne.{1} NLogN.Cls (NLogN.cls (@List.head?.{0} NLogN.Item tail)) NLogN.Cls.mark)
  (hs :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G S s src)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.replicate.{0} NLogN.Item m NLogN.Item.mark) tail)),
  @NLogN.IExec S (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) I
    (@Fin.elim0.{1} (NLogN.IStmt S (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@KoanaKPaths.Machine.moveMarks S src dst) s
    (@NLogN.IState.upd S (@NLogN.IState.upd S s src tail) dst
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.replicate.{0} NLogN.Item m NLogN.Item.mark) (@NLogN.IState.G S s dst)))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32))) m)
      (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))) := by sorry
