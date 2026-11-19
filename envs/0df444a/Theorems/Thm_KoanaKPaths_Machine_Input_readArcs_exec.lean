-- Prove2me | Theorems.Thm_KoanaKPaths_Machine_Input_readArcs_exec
-- name    : KoanaKPaths.Machine.Input.readArcs_exec
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T08:12:22.822487+00:00
-- url     : https://prove2.me/theorems/7e9c887e-8d03-44fa-8bce-ddef0894dd25
-- title:
--   Parse a directed arc list with exact bit-input cost
-- statement:
--   Let $P=[(u_1,v_1),\ldots,(u_m,v_m)]$ be a list of endpoint pairs. Suppose the input head points immediately before their binary arc encoding and a unary counter contains $m$ markers. The arc-reading loop consumes exactly that encoding, empties its counter and prepends the corresponding database records:
--   $$
--   \operatorname{DB}_{\rm final}=\operatorname{arcItems}(P)\mathbin{+\!+}\operatorname{DB}_{\rm initial}.
--   $$
--   The stored records use the stack's reversed list order, with each physical record containing the second endpoint, first endpoint and delimiter. The exact cost is
--   $$
--   C([])=1,\quad C((u,v)::P)=11|\operatorname{bits}(u)|+11|\operatorname{bits}(v)|+15+C(P).
--   $$
--   The input suffix, output and unrelated stacks are preserved. This specifies the native parser used to build the graph database from a plain arc-list input.
-- source:
--   T. Koana, Approximate Counting of k-Paths in O*(2^k) Time, STOC 2027 submission #953, October 2026, §3.2 (printed pp. 8–9 / PDF pp. 9–10) and §4.1 (printed p. 9 / PDF p. 10), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/953.pdf. Native implementation: Solutions/ArcInput.lean, line 32; source snapshot SHA-256 7a5f40c0ee7853401b77bb6533effe4c9b70049a4ecb8a75ec8cd9bd3eb82399.

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
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem KoanaKPaths.Machine.Input.readArcs_exec :
∀ {P : Nat} (I : List.{0} NLogN.Sym)
  (prog :
    Fin P →
      NLogN.Stmt
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) KoanaKPaths.Machine.Input.NS
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
        P)
  (arcs : List.{0} (Prod.{0, 0} Nat Nat)) (s : NLogN.IState KoanaKPaths.Machine.Input.NS)
  (pre post : List.{0} NLogN.Sym)
  (hc :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Input.NS s KoanaKPaths.Machine.Input.Counter)
      (@List.replicate.{0} NLogN.Item (@List.length.{0} (Prod.{0, 0} Nat Nat) arcs) NLogN.Item.mark))
  (hI :
    @Eq.{1} (List.{0} NLogN.Sym) I
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Sym) (List.{0} NLogN.Sym) (List.{0} NLogN.Sym)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Sym) (@List.instAppend.{0} NLogN.Sym))
        (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Sym) (List.{0} NLogN.Sym) (List.{0} NLogN.Sym)
          (@instHAppendOfAppend.{0} (List.{0} NLogN.Sym) (@List.instAppend.{0} NLogN.Sym)) pre
          (KoanaKPaths.Machine.Input.arcSymbols arcs))
        post))
  (hip : @Eq.{1} Nat (@NLogN.IState.ip KoanaKPaths.Machine.Input.NS s) (@List.length.{0} NLogN.Sym pre)),
  @NLogN.Exec
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) KoanaKPaths.Machine.Input.NS
      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
    P I prog (@KoanaKPaths.Machine.Input.readArcs P) (@NLogN.encI KoanaKPaths.Machine.Input.NS s)
    (@NLogN.encI KoanaKPaths.Machine.Input.NS
      (have __src : NLogN.IState KoanaKPaths.Machine.Input.NS :=
        @NLogN.IState.upd KoanaKPaths.Machine.Input.NS
          (@NLogN.IState.upd KoanaKPaths.Machine.Input.NS s KoanaKPaths.Machine.Input.Counter
            (@List.nil.{0} NLogN.Item))
          KoanaKPaths.Machine.Input.DB
          (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
            (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
            (KoanaKPaths.Machine.Input.arcItems arcs)
            (@NLogN.IState.G KoanaKPaths.Machine.Input.NS s KoanaKPaths.Machine.Input.DB));
      @NLogN.IState.mk KoanaKPaths.Machine.Input.NS (@NLogN.IState.G KoanaKPaths.Machine.Input.NS __src)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@NLogN.IState.ip KoanaKPaths.Machine.Input.NS s)
          (@List.length.{0} NLogN.Sym (KoanaKPaths.Machine.Input.arcSymbols arcs)))
        (@NLogN.IState.out KoanaKPaths.Machine.Input.NS __src)))
    (KoanaKPaths.Machine.Input.arcCost arcs) := by sorry
