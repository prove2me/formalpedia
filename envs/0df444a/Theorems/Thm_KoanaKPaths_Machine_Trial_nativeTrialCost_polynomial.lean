-- Prove2me | Theorems.Thm_KoanaKPaths_Machine_Trial_nativeTrialCost_polynomial
-- name    : KoanaKPaths.Machine.Trial.nativeTrialCost_polynomial
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T08:11:25.437899+00:00
-- url     : https://prove2.me/theorems/6f77f95a-c4c5-4e52-9ba2-5fddce9b034a
-- title:
--   Singly exponential polynomial bound for one complete native trial
-- statement:
--   For a graph with $n$ vertices and $m$ stored arcs, and for every path parameter $k\ge1$, the declared cost of one complete native estimator trial satisfies
--   $$
--   C_{\rm trial}(n,k,m)\le10^{15}2^k(1+n+k+m)^{10}.
--   $$
--   The trial schedule includes sign loading, the exterior-coordinate graph dynamic program, squared-norm extraction and cleanup. It is a worst-case deterministic cost bound for every supplied sign tape, independent of any accuracy or probability estimate. Group repetition, median amplification, initial graph parsing and the final bit-machine adapter are accounted for separately. This lemma is the basic cost input for the overall approximation algorithm's $O^*(2^k)$ bound, with arithmetic charged by encoded integer widths rather than unit cost.
-- source:
--   T. Koana, Approximate Counting of k-Paths in O*(2^k) Time, STOC 2027 submission #953, October 2026, §3.2 (printed pp. 8–9 / PDF pp. 9–10) and §4.1 (printed p. 9 / PDF p. 10), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/953.pdf. Native implementation: Solutions/NativeTrialCostBound.lean, line 10; source snapshot SHA-256 61ddc4468d55b895f75754e687572a83b01bbd28a5725e3d74164e0c6ee3eb76.

import Definitions.Def_HypergraphUnreliability_FPRAS_Machine
import Definitions.Def_IntMul_SS_Defs1
import Definitions.Def_IntMul_SS_Defs2
import Definitions.Def_KoanaKPaths_BitStackAdapter
import Definitions.Def_KoanaKPaths_ExteriorCoordinates
import Definitions.Def_KoanaKPaths_GraphDP
import Definitions.Def_KoanaKPaths_Main_Estimator
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

theorem KoanaKPaths.Machine.Trial.nativeTrialCost_polynomial :
∀ (n k m : Nat) (hk : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) k),
  @LE.le.{0} Nat instLENat (KoanaKPaths.Machine.Trial.nativeTrialCost n k m)
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 1000000000000000) (instOfNatNat (nat_lit 1000000000000000)))
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k))
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) n)
            k)
          m)
        (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))))) := by sorry
