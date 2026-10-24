-- Prove2me | Theorems.Thm_OAI_QuadricCounterexample_DiskSubharmonicOn_of_C2_laplacian_nonneg
-- name    : OAI.QuadricCounterexample.DiskSubharmonicOn.of_C2_laplacian_nonneg
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T15:57:36.62532+00:00
-- url     : https://prove2.me/theorems/7fdac597-6ef4-4a52-b73b-1bff5b5b6dca
-- title:
--   A C² function in the plane with nonnegative Laplacian is subharmonic (disk submean inequality)
-- statement:
--   The definitions are from the definitions bundle `OAIQWQC000`:
--   - `complexLaplacian u z` is $\Delta u(z) = D^2u(z)(1, 1) + D^2u(z)(i, i)$, the sum of the second real derivatives of $u : \mathbb C \to \mathbb R$ in the directions $1$ and $i$ (iterated Fréchet derivatives over $\mathbb R$);
--   - `DiskSubharmonicOn Ω u` means that $u$ is upper semicontinuous on $\Omega$ and, for every $x \in \Omega$ and $r > 0$ with $\overline B(x, r) \subseteq \Omega$, integrable on $B(x, r)$ with $|B(x, r)|\,u(x) \le \int_{B(x,r)} u$.
--
--   **Statement.** Let $D \subseteq \mathbb C$ be open and $u : \mathbb C \to \mathbb R$ be $C^2$ on $D$ (`ContDiffOn ℝ 2 u D`) with $\Delta u(z) \ge 0$ for every $z \in D$. Then `DiskSubharmonicOn D u`.
--
--   $$u \in C^2(D),\quad \Delta u \ge 0 \text{ on } D \;\Longrightarrow\; |B(x,r)|\,u(x) \le \int_{B(x,r)} u \quad \text{whenever } \overline B(x,r) \subseteq D.$$
--
--   This is the classical fact that a $C^2$ function with nonnegative Laplacian is subharmonic (see Ransford, *Potential Theory in the Complex Plane*, Section 2.4).
--
--   Lean: `OAI.QuadricCounterexample.DiskSubharmonicOn.of_C2_laplacian_nonneg`, OpenAI's theorem of that name (in `lean/OAI/Geometry/QuadricBundles/Plurisubharmonic.lean`). The statement imports only the small definitions bundle `OAIQWQC000` of this split. A definition of OpenAI's development needs it (through `DiskPshOn.of_C2_leviTrace_nonneg`), so a later definitions bundle of this split imports this statement instead of proving it again.
-- source:
--   classical (subharmonicity of C² functions with Δu ≥ 0; see T. Ransford, Potential Theory in the Complex Plane, Cambridge University Press, 1995, Section 2.4); proof and Lean code: OpenAI, Ample rank-two bundles on the quadric surface without Griffiths-positive metrics, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 050; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/ample-rank-two-bundles-on-the-quadric-surface-without-griffiths-positive-metrics-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/QuadricBundles/Plurisubharmonic.lean (declaration OAI.QuadricCounterexample.DiskSubharmonicOn.of_C2_laplacian_nonneg)

import Mathlib
import Definitions.Def_OAIQWQC000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11

namespace QuadricCounterexample
open Set Filter Topology Metric MeasureTheory
noncomputable section
open scoped Pointwise

attribute [local instance] Measure.Subtype.measureSpace

attribute [local instance] OAI.QuadricCounterexample.realDualComplexGroup
attribute [local instance] OAI.QuadricCounterexample.realDualComplexSpace
theorem DiskSubharmonicOn.of_C2_laplacian_nonneg {u : ℂ → ℝ} {D : Set ℂ}
    (hD : IsOpen D) (hu : ContDiffOn ℝ 2 u D) (hΔ : ∀ z∈D, 0≤complexLaplacian u z) :
    DiskSubharmonicOn D u := by
  sorry

end
end QuadricCounterexample

end OAI
end
