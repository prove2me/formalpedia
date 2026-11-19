-- Prove2me | Theorems.Thm_KoanaKPaths_Main_graphLayer_natAbs
-- name    : KoanaKPaths.Main.graphLayer_natAbs
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T08:18:38.534562+00:00
-- url     : https://prove2.me/theorems/d2435285-cd6d-4bd2-b14f-c75a60fb4097
-- title:
--   Uniform absolute-value bound for every graph-sketch layer coordinate
-- statement:
--   For a graph arc list $A$ on $n$ vertices, exterior dimension $k$, sketch width $\ell$, arbitrary label signs $\sigma$, and sketch signs $R$, let $D_p(v,a)_S$ be the exterior coordinate indexed by $S\subseteq[k]$ in graph layer $p$. For every natural $p$, vertex $v<n$, and state $a<\ell$,
--   $$\bigl|D_p(v,a)_S\bigr|\le\bigl(1+k(n\ell+1)\bigr)^p.$$
--   Absolute value here is the natural absolute value of an integer. No simplicity or duplicate-free condition is needed on the arc list. The recurrence uses arc-set membership, signed predecessor sums, and one right wedge with vertex labels. This bound controls the bit lengths of every array entry during the native graph-sketch computation.
-- source:
--   T. Koana, Approximate Counting of k-Paths in O*(2^k) Time, STOC 2027 submission #953, October 2026, §3.2 (printed pp. 8–9 / PDF pp. 9–10) and §4.1 (printed p. 9 / PDF p. 10), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/953.pdf. Native implementation: Solutions/GraphSize.lean, line 42; source snapshot SHA-256 23d6c11f971950caa08a3e268e78a0e2d14fb5192a400116a3aa931a192d3d10.

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
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem KoanaKPaths.Main.graphLayer_natAbs :
∀ {n k ℓ : Nat} (arcs : List.{0} (Prod.{0, 0} (Fin n) (Fin n))) (σ : KoanaKPaths.Main.Labels n k)
  (R : KoanaKPaths.Main.SketchSigns n k ℓ) (p : Nat) (v : Fin n) (a : Fin ℓ) (S : Finset.{0} (Fin k)),
  @LE.le.{0} Nat instLENat (Int.natAbs (@KoanaKPaths.Main.graphLayer n k ℓ arcs σ R p v a S))
    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
      (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
      (KoanaKPaths.Main.layerRadius n k ℓ) p) := by sorry
