-- Prove2me | Theorems.Thm_KoanaKPaths_Machine_Trial_readSign_runs
-- name    : KoanaKPaths.Machine.Trial.readSign_runs
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T08:13:33.191202+00:00
-- url     : https://prove2.me/theorems/133ae04a-066d-4f70-b372-1b8df2b537ae
-- title:
--   Reading a sign at an arithmetically computed cached address
-- statement:
--   Let $X$ be a cached list of signs, and let $e$ be a natural arithmetic expression over readonly input registers. Suppose its value $j=\operatorname{eval}(e)$ satisfies $j<|X|$, its intermediate width and the cached-length header fit $w\ge1$, no input register is the evaluation register, and lookup helpers are empty. The sign-reading program changes only its sign-output stack:
--   $$\operatorname{Out}_{\rm after}=X_j::\operatorname{Out}_{\rm before},\qquad t\le30000(|e|+2)(w+1)^2+10000(|X|+1).$$
--   The database, inputs, helper tails, input position, and external output are preserved. This makes shared trial signs accessible by graph and sketch indices with explicit bit time.
-- source:
--   T. Koana, Approximate Counting of k-Paths in O*(2^k) Time, STOC 2027 submission #953, October 2026, §3.2 (printed pp. 8–9 / PDF pp. 9–10) and §4.1 (printed p. 9 / PDF p. 10), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/953.pdf. Native implementation: Solutions/SignRead.lean, line 15; source snapshot SHA-256 f30f7755b75f6f37b1db2e0aea1efd0802dd38ef61eb3940c3f43e5c2a0f61b0.

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
import Theorems.Thm_NLogN_smul_runs
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem KoanaKPaths.Machine.Trial.readSign_runs :
∀ {v : Nat} (I : List.{0} NLogN.Sym) (reg : Fin v → Fin KoanaKPaths.Machine.Trial.NS)
  (hreg : ∀ (i : Fin v), @Ne.{1} (Fin KoanaKPaths.Machine.Trial.NS) (reg i) KoanaKPaths.Machine.Square.Eval)
  (values : Fin v → Nat) (e : KoanaKPaths.Machine.Arithmetic.Expr v) (xs : List.{0} Int) (w : Nat)
  (hw : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) w)
  (he : @LE.le.{0} Nat instLENat (@KoanaKPaths.Machine.Arithmetic.Expr.width v values e) w)
  (hT : @LE.le.{0} Nat instLENat (NLogN.zsz (@Nat.cast.{0} Int instNatCastInt (@List.length.{0} Int xs))) w)
  (hj : @LT.lt.{0} Nat instLTNat (@KoanaKPaths.Machine.Arithmetic.Expr.eval v values e) (@List.length.{0} Int xs))
  (s : NLogN.IState KoanaKPaths.Machine.Trial.NS) (tt rest : List.{0} NLogN.Item)
  (hTotal :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.Total)
      (@List.cons.{0} NLogN.Item (NLogN.Item.int (@Nat.cast.{0} Int instNatCastInt (@List.length.{0} Int xs))) tt))
  (hv :
    ∀ (i : Fin v),
      @Exists.{1} (List.{0} NLogN.Item) fun (tail : List.{0} NLogN.Item) =>
        @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s (reg i))
          (@List.cons.{0} NLogN.Item (NLogN.Item.int (@Nat.cast.{0} Int instNatCastInt (values i))) tail))
  (hc :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.BitCounter.Count)
      (@List.nil.{0} NLogN.Item))
  (ht :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.BitCounter.Tmp)
      (@List.nil.{0} NLogN.Item))
  (hindex :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.SignLookup.Count)
      (@List.nil.{0} NLogN.Item))
  (hback :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.SignLookup.Back)
      (@List.nil.{0} NLogN.Item))
  (htmp :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.SignLookup.Tmp)
      (@List.nil.{0} NLogN.Item))
  (hdb :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.SignDB)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (KoanaKPaths.Machine.Trial.signItems xs) rest))
  (hxs :
    ∀ (x : Int),
      @Membership.mem.{0, 0} Int (List.{0} Int) (@List.instMembership.{0} Int) xs x →
        Or (@Eq.{1} Int x (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (@Eq.{1} Int x
            (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))),
  @NLogN.IRuns KoanaKPaths.Machine.Trial.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) I
    (@Fin.elim0.{1}
      (NLogN.IStmt KoanaKPaths.Machine.Trial.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@KoanaKPaths.Machine.Trial.readSign v reg e) s
    (@NLogN.IState.upd KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.SignLookup.Out
      (@List.cons.{0} NLogN.Item
        (NLogN.Item.int
          (@GetElem.getElem.{0, 0, 0} (List.{0} Int) Nat Int
            (fun (as : List.{0} Int) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Int as))
            (@List.instGetElemNatLtLength.{0} Int) xs (@KoanaKPaths.Machine.Arithmetic.Expr.eval v values e) hj))
        (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.SignLookup.Out)))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 30000) (instOfNatNat (nat_lit 30000)))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@KoanaKPaths.Machine.Arithmetic.Expr.size v e)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) w
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 10000) (instOfNatNat (nat_lit 10000)))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} Int xs)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) := by sorry
