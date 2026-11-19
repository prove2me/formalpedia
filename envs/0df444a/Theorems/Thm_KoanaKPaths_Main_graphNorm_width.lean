-- Prove2me | Theorems.Thm_KoanaKPaths_Main_graphNorm_width
-- name    : KoanaKPaths.Main.graphNorm_width
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T08:14:51.145066+00:00
-- url     : https://prove2.me/theorems/da6e45c5-88c0-4947-9911-997e52b5d399
-- title:
--   A deterministic bit-width bound for the squared graph-sketch norm
-- statement:
--   Let a graph on $n$ vertices, dimension $k$, sketch width $\ell$, vertex signs $\sigma$ and sketch signs $R$ be arbitrary. For each state $a<\ell$, let $G_a([k])$ be the full-set exterior coefficient of the graph-sketch output. Define the nonnegative integer
--   $$
--   Z=\sum_{a<\ell}G_a([k])^2.
--   $$
--   Its native integer width $\beta$ satisfies
--   $$
--   \beta(Z)\le\ell+2\bigl(n+(n+k+\ell+3)k\bigr)+1.
--   $$
--   This bound is pointwise in all signs and includes zero dimensions, empty graphs and zero outputs. No probabilistic moment estimate is used. It controls the bit size of each actual trial numerator, providing the finite-width arithmetic bounds required by native squaring, group accumulation and rational-output construction.
-- source:
--   T. Koana, Approximate Counting of k-Paths in O*(2^k) Time, STOC 2027 submission #953, October 2026, §3.2 (printed pp. 8–9 / PDF pp. 9–10) and §4.1 (printed p. 9 / PDF p. 10), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/953.pdf. Native implementation: Solutions/NormBounds.lean, line 20; source snapshot SHA-256 8cdefd114ab703f03684a9dc9e91227d4d26c3dddcfb5007d148b94754c3ea66.

import Definitions.Def_HypergraphUnreliability_FPRAS_Machine
import Definitions.Def_IntMul_SS_Defs1
import Definitions.Def_IntMul_SS_Defs2
import Definitions.Def_KoanaKPaths_ExteriorCoordinates
import Definitions.Def_KoanaKPaths_GraphDP
import Definitions.Def_KoanaKPaths_Runtime_LiftNative
import Definitions.Def_KoanaKPaths_Runtime_NatParser
import Definitions.Def_KoanaKPaths_Runtime_NativeProgram
import Definitions.Def_KoanaKPaths_Runtime_SubsetArrays
import Definitions.Def_KoanaKPaths_Runtime_TrialIndexing
import Mathlib
import Mathlib.Data.Nat.Size
import Theorems.Thm_KoanaKPaths_Main_graph_dp_sketch
import Theorems.Thm_NLogN_smul_runs
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem KoanaKPaths.Main.graphNorm_width :
∀ {n k ℓ : Nat} (arcs : List.{0} (Prod.{0, 0} (Fin n) (Fin n))) (σ : KoanaKPaths.Main.Labels n k)
  (R : KoanaKPaths.Main.SketchSigns n k ℓ),
  @LE.le.{0} Nat instLENat
    (NLogN.zsz
      (@Finset.sum.{0, 0} (Fin ℓ) Int Int.instAddCommMonoid (@Finset.univ.{0} (Fin ℓ) (Fin.fintype ℓ))
        fun (a : Fin ℓ) =>
        @HPow.hPow.{0, 0, 0} Int Nat Int
          (@instHPow.{0, 0} Int Nat (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid)))
          (@KoanaKPaths.Main.graphOutput n k ℓ arcs σ R a (@Finset.univ.{0} (Fin k) (Fin.fintype k)))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (KoanaKPaths.Main.trialWidth n k ℓ) := by sorry
