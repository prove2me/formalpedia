-- Prove2me | Theorems.Thm_KoanaKPaths_Machine_Trial_wholeCost_budget
-- name    : KoanaKPaths.Machine.Trial.wholeCost_budget
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T08:14:56.175438+00:00
-- url     : https://prove2.me/theorems/e7db99f2-249c-4790-8eb6-42a536cc3831
-- title:
--   Uniform singly exponential budget for native graph counting and output
-- statement:
--   Let $n,k,a,b$ be natural parameters with $k\ge1$, let the input graph have any arc list, and let the supplied coin tape be arbitrary. Write $L$ for the binary graph-code length, excluding $k$ and tolerance controls. Let $C_{\rm root}$ be the native whole-program execution charge and $\widehat N$ the rational estimate determined by this tape. Then
--   $$
--   C_{\rm root}+|\operatorname{fracCode}(\widehat N)|+2
--   \le10^{28}2^k(1+k+n+L)^{20}4^a(b+1).
--   $$
--   The left side includes the final rational output length and a constant finalization allowance. No randomness, simplicity or positivity of the actual path count is assumed for this deterministic cost bound. It combines graph parsing, control setup, sign sampling, amplified estimation and output accounting into the budget later transferred to the fair-bit machine.
-- source:
--   T. Koana, Approximate Counting of k-Paths in O*(2^k) Time, STOC 2027 submission #953, October 2026, §3.2 (printed pp. 8–9 / PDF pp. 9–10) and §4.1 (printed p. 9 / PDF p. 10), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/953.pdf. Native implementation: Solutions/WholeCost.lean, line 26; source snapshot SHA-256 bb17fc66db1b5999b87e164401dc2f2c936501b688663f3afc5d55bd64ff16a5.

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

theorem KoanaKPaths.Machine.Trial.wholeCost_budget :
∀ (n : Nat) (arcs : List.{0} (Prod.{0, 0} (Fin n) (Fin n))) (k a b : Nat) (tape : List.{0} Bool)
  (hk : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) k),
  @LE.le.{0} Nat instLENat
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (KoanaKPaths.Machine.Trial.rootCost n arcs k a b tape)
        (@List.length.{0} Bool
          (HypergraphUnreliability.FPRAS.fracCode (KoanaKPaths.Main.tapeEstimate n arcs k a b tape))))
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (KoanaKPaths.Main.timeBudget
      (@OfNat.ofNat.{0} Nat (nat_lit 10000000000000000000000000000)
        (instOfNatNat (nat_lit 10000000000000000000000000000)))
      (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))) k
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
        (@List.length.{0} Bool (KoanaKPaths.Main.graphCode n arcs)))
      a b) := by sorry
