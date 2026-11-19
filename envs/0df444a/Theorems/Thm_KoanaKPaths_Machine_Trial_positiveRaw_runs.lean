-- Prove2me | Theorems.Thm_KoanaKPaths_Machine_Trial_positiveRaw_runs
-- name    : KoanaKPaths.Machine.Trial.positiveRaw_runs
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T08:19:45.971556+00:00
-- url     : https://prove2.me/theorems/3ddc441d-b83d-476f-a629-1a0d60cc0d06
-- title:
--   Compiled estimator execution from parsed input to rational output
-- statement:
--   Let $A$ be a graph on $n$ vertices, let $k\ge1$, and let $a,b$ be natural controls. Suppose the random tape contains at least $S=\operatorname{sampleBits}(n,k,a,b)$ bits. Starting from the encoded parsed-input state, the compiled positive-parameter program has a terminating execution whose output is
--   $$\operatorname{fracCode}\bigl(\operatorname{estimateFraction}(\operatorname{walkTensor}(A,k),a,b,\operatorname{tapeSamples})\bigr).$$
--   It runs within the explicit bound $\operatorname{positiveCost}$: setup cost, separator skip, $8S+2$ for loading bits as signs, native estimator cost, and fraction-writing cost. The sample uses the tape's first $S$ bits. This joins native arithmetic correctness to an actual bit-input, bit-output stack program.
-- source:
--   T. Koana, Approximate Counting of k-Paths in O*(2^k) Time, STOC 2027 submission #953, October 2026, §3.2 (printed pp. 8–9 / PDF pp. 9–10) and §4.1 (printed p. 9 / PDF p. 10), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/953.pdf. Native implementation: Solutions/PositiveRaw.lean, line 30; source snapshot SHA-256 d9625e05e4614db67d2a958581b2525e9c9068af91bc26ff6843291023699315.

import Definitions.Def_HypergraphUnreliability_FPRAS_Machine
import Definitions.Def_IntMul_SS_Defs1
import Definitions.Def_IntMul_SS_Defs2
import Definitions.Def_KoanaKPaths_BitStackAdapter
import Definitions.Def_KoanaKPaths_ExteriorCoordinates
import Definitions.Def_KoanaKPaths_GraphDP
import Definitions.Def_KoanaKPaths_Main_Estimator
import Definitions.Def_KoanaKPaths_MedianOfMeans
import Definitions.Def_KoanaKPaths_Runtime_LiftNative
import Definitions.Def_KoanaKPaths_Runtime_NatParser
import Definitions.Def_KoanaKPaths_Runtime_NativeProgram
import Definitions.Def_KoanaKPaths_Runtime_SubsetArrays
import Definitions.Def_KoanaKPaths_Runtime_TrialIndexing
import Definitions.Def_KoanaKPaths_TapeSampling
import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Size
import Theorems.Thm_KoanaKPaths_Main_graph_dp_sketch
import Theorems.Thm_NLogN_compile_correct
import Theorems.Thm_NLogN_smul_runs
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem KoanaKPaths.Machine.Trial.positiveRaw_runs :
∀ (n : Nat) (arcs : List.{0} (Prod.{0, 0} (Fin n) (Fin n))) (k a b : Nat) (tape : List.{0} Bool)
  (hk : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) k)
  (hTape : @LE.le.{0} Nat instLENat (KoanaKPaths.Main.sampleBits n k a b) (@List.length.{0} Bool tape)),
  @Exists.{1}
    (NLogN.St
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) KoanaKPaths.Machine.Trial.NS
        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
    fun
      (σ :
        NLogN.St
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) KoanaKPaths.Machine.Trial.NS
            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))) =>
    And
      (@NLogN.Runs
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) KoanaKPaths.Machine.Trial.NS
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
        (KoanaKPaths.Machine.logicalInput (KoanaKPaths.Main.graphInputControls n arcs k a b) tape)
        KoanaKPaths.Machine.Trial.rawProg KoanaKPaths.Machine.Trial.positiveRaw
        (@NLogN.encI KoanaKPaths.Machine.Trial.NS (KoanaKPaths.Machine.Input.parsedState n arcs k a b)) σ
        (KoanaKPaths.Machine.Trial.positiveCost n arcs k a b tape))
      (@Eq.{1} (List.{0} Bool)
        (@NLogN.St.out
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) KoanaKPaths.Machine.Trial.NS
            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
          σ)
        (HypergraphUnreliability.FPRAS.fracCode
          (@KoanaKPaths.Main.estimateFraction n k (KoanaKPaths.Main.walkTensor n arcs k) a b
            (KoanaKPaths.Main.tapeSamples n k a b tape)))) := by sorry
