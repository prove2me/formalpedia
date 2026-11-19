-- Prove2me | Theorems.Thm_KoanaKPaths_Machine_Trial_loadLoop_exec
-- name    : KoanaKPaths.Machine.Trial.loadLoop_exec
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T08:13:31.787194+00:00
-- url     : https://prove2.me/theorems/ed1f74e6-63f7-47a1-849e-2712546d7c13
-- title:
--   Caching a finite stream of native integer signs
-- statement:
--   Let $X=(x_1,\ldots,x_m)$ be any integer list on the coin stack above a tail, and suppose the sign counter contains $m$ unary markers. The loading loop consumes precisely this list, empties the counter, and prepends singleton marked frames to the sign database in reverse order:
--   $$\operatorname{SignDB}_{\rm after}=[x_m,\#]\cdots[x_1,\#]\mathbin{+\!+}\operatorname{SignDB}_{\rm before}.$$
--   Its exact bit charge is $\sum_{x\in X}(2\operatorname{moveCost}(\operatorname{bits}(x))+51)+30$. The theorem does not require $x_j=\pm1$. All original tails, other registers, input position, and output are preserved. Specializing to signs caches the random block for repeated shared-sign access.
-- source:
--   T. Koana, Approximate Counting of k-Paths in O*(2^k) Time, STOC 2027 submission #953, October 2026, §3.2 (printed pp. 8–9 / PDF pp. 9–10) and §4.1 (printed p. 9 / PDF p. 10), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/953.pdf. Native implementation: Solutions/TrialSigns.lean, line 27; source snapshot SHA-256 edd54ff2ca050fbbfd5dfee0e48c2e4c00b8bbca579c9f75c28220bf6b8b8b6e.

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

theorem KoanaKPaths.Machine.Trial.loadLoop_exec :
∀ (I : List.{0} NLogN.Sym) (s : NLogN.IState KoanaKPaths.Machine.Trial.NS) (xs : List.{0} Int)
  (tail : List.{0} NLogN.Item)
  (hc :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.SignCounter)
      (@List.replicate.{0} NLogN.Item (@List.length.{0} Int xs) NLogN.Item.mark))
  (hs :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.Coins)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.map.{0, 0} Int NLogN.Item NLogN.Item.int xs) tail)),
  @NLogN.IExec KoanaKPaths.Machine.Trial.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) I
    (@Fin.elim0.{1}
      (NLogN.IStmt KoanaKPaths.Machine.Trial.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    KoanaKPaths.Machine.Trial.loadLoop s
    (@NLogN.IState.upd KoanaKPaths.Machine.Trial.NS
      (@NLogN.IState.upd KoanaKPaths.Machine.Trial.NS
        (@NLogN.IState.upd KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.SignCounter
          (@List.nil.{0} NLogN.Item))
        KoanaKPaths.Machine.Trial.Coins tail)
      KoanaKPaths.Machine.Trial.SignDB
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (KoanaKPaths.Machine.Trial.signItems xs)
        (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.SignDB)))
    (KoanaKPaths.Machine.Trial.loadCost xs) := by sorry
