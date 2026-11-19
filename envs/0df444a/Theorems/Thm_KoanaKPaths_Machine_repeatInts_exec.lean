-- Prove2me | Theorems.Thm_KoanaKPaths_Machine_repeatInts_exec
-- name    : KoanaKPaths.Machine.repeatInts_exec
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T08:10:47.281932+00:00
-- url     : https://prove2.me/theorems/ab4665b0-68ec-4cdc-a2b8-1db12626bf63
-- title:
--   Build a constant integer array from a unary length
-- statement:
--   Let the unary count register and integer destination register be distinct. Suppose the count stack begins with $m$ markers followed by a nonmarker tail, and let $z$ be any signed integer. The repeat-integers program consumes the marker prefix and prepends exactly $m$ copies of $z$:
--   $$
--   \operatorname{Count}'=\mathrm{tail},\qquad\operatorname{Dst}'=[z]^{m}\mathbin{+\!+}\operatorname{Dst}.
--   $$
--   It preserves all other state and saved tails. With $\beta(z)$ denoting the native integer width, its exact charged running time is
--   $$
--   (\beta(z)+33)m+30.
--   $$
--   The assertion includes $m=0$ and arbitrary destination contents. This construction initializes zero coefficient arrays and other constant-valued native buffers with an explicitly charged cost per coordinate.
-- source:
--   T. Koana, Approximate Counting of k-Paths in O*(2^k) Time, STOC 2027 submission #953, October 2026, §3.2 (printed pp. 8–9 / PDF pp. 9–10) and §4.1 (printed p. 9 / PDF p. 10), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/953.pdf. Native implementation: Solutions/NativeRepeat.lean, line 13; source snapshot SHA-256 681e3a6718c4a2444545bb71a029c9d51af9d6b2cc4192965daf826fe3a63395.

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

theorem KoanaKPaths.Machine.repeatInts_exec :
∀ {S : Nat} (I : List.{0} NLogN.Sym) (count dst : Fin S) (hne : @Ne.{1} (Fin S) count dst) (z : Int)
  (s : NLogN.IState S) (m : Nat) (tail : List.{0} NLogN.Item)
  (ht : @Ne.{1} NLogN.Cls (NLogN.cls (@List.head?.{0} NLogN.Item tail)) NLogN.Cls.mark)
  (hc :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G S s count)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.replicate.{0} NLogN.Item m NLogN.Item.mark) tail)),
  @NLogN.IExec S (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) I
    (@Fin.elim0.{1} (NLogN.IStmt S (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@KoanaKPaths.Machine.repeatInts S count dst z) s
    (@NLogN.IState.upd S (@NLogN.IState.upd S s count tail) dst
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.replicate.{0} NLogN.Item m (NLogN.Item.int z)) (@NLogN.IState.G S s dst)))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (NLogN.zsz z)
          (@OfNat.ofNat.{0} Nat (nat_lit 33) (instOfNatNat (nat_lit 33))))
        m)
      (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))) := by sorry
