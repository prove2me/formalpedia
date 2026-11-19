-- Prove2me | Theorems.Thm_KoanaKPaths_Machine_Input_readGraph_runs
-- name    : KoanaKPaths.Machine.Input.readGraph_runs
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T08:15:46.947331+00:00
-- url     : https://prove2.me/theorems/34c7b829-4b71-4de8-981c-a79796a1aa83
-- title:
--   Parsing a graph and tolerance controls into native machine registers
-- statement:
--   For a graph on $n$ vertices with an arc list $A$, path parameter $k$, natural controls $a,b$, and arbitrary tape, the graph-reading program starts with empty raw stacks and parses the encoded graph input. It reaches the encoded parsed state containing the five headers $n,k,a,b,|A|$ and the arc database, with
--   $$\operatorname{ip}_{\rm after}=|\operatorname{graphInputControls}(n,A,k,a,b)|,\qquad t\le\operatorname{graphReadCost}(n,A,k,a,b).$$
--   The bound is the header-field parsing charge plus $2000(|A|+1)$ and the arc-record parsing charge. The external output remains empty. This contract isolates deterministic input decoding from later random-tape consumption and estimator execution.
-- source:
--   T. Koana, Approximate Counting of k-Paths in O*(2^k) Time, STOC 2027 submission #953, October 2026, §3.2 (printed pp. 8–9 / PDF pp. 9–10) and §4.1 (printed p. 9 / PDF p. 10), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/953.pdf. Native implementation: Solutions/GraphInput.lean, line 54; source snapshot SHA-256 b6b1a8359ea4a947b6e5212386c49bc0c9bd5b1917ae38b93028a1c97185a5ca.

import Definitions.Def_HypergraphUnreliability_FPRAS_Machine
import Definitions.Def_IntMul_SS_Defs1
import Definitions.Def_IntMul_SS_Defs2
import Definitions.Def_KoanaKPaths_BitStackAdapter
import Definitions.Def_KoanaKPaths_ExteriorCoordinates
import Definitions.Def_KoanaKPaths_Main_Estimator
import Definitions.Def_KoanaKPaths_Runtime_LiftNative
import Definitions.Def_KoanaKPaths_Runtime_NatParser
import Definitions.Def_KoanaKPaths_Runtime_NativeProgram
import Definitions.Def_KoanaKPaths_Runtime_SubsetArrays
import Definitions.Def_KoanaKPaths_Runtime_TrialIndexing
import Definitions.Def_KoanaKPaths_TapeSampling
import Mathlib
import Mathlib.Data.Nat.Size
import Theorems.Thm_NLogN_compile_correct
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem KoanaKPaths.Machine.Input.readGraph_runs :
∀ {P : Nat}
  (prog :
    Fin P →
      NLogN.Stmt
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) KoanaKPaths.Machine.Input.NS
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
        P)
  (iprog : Fin P → NLogN.IStmt KoanaKPaths.Machine.Input.NS P)
  (hprog :
    ∀ (j : Fin P),
      @Eq.{1}
        (NLogN.Stmt
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) KoanaKPaths.Machine.Input.NS
            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
          P)
        (prog j) (@NLogN.compile KoanaKPaths.Machine.Input.NS P (iprog j)))
  (n : Nat) (arcs : List.{0} (Prod.{0, 0} (Fin n) (Fin n))) (k a b : Nat) (tape : List.{0} Bool),
  @NLogN.Runs
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) KoanaKPaths.Machine.Input.NS
      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
    P (KoanaKPaths.Machine.logicalInput (KoanaKPaths.Main.graphInputControls n arcs k a b) tape) prog
    (@KoanaKPaths.Machine.Input.readGraph P)
    (NLogN.St.init
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) KoanaKPaths.Machine.Input.NS
        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
    (@NLogN.encI KoanaKPaths.Machine.Input.NS (KoanaKPaths.Machine.Input.parsedState n arcs k a b))
    (KoanaKPaths.Machine.Input.graphReadCost n arcs k a b) := by sorry
