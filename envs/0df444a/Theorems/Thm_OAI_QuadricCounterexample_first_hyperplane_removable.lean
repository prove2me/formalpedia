-- Prove2me | Theorems.Thm_OAI_QuadricCounterexample_first_hyperplane_removable
-- name    : OAI.QuadricCounterexample.first_hyperplane_removable
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T15:58:30.125286+00:00
-- url     : https://prove2.me/theorems/bbb9785d-a2c8-453b-bd5b-943bacf78ba3
-- title:
--   Removability of a coordinate hyperplane for continuous nonnegative plurisubharmonic functions
-- statement:
--   The definitions are from the definitions bundles `OAIQWQC000` and `OAIQWQC001`:
--   - `DiskSubharmonicOn D u` (for $D \subseteq \mathbb C$) means that $u$ is upper semicontinuous on $D$ and satisfies the disk submean inequality $|B(x, r)|\,u(x) \le \int_{B(x,r)} u$ (with $u$ integrable on $B(x,r)$) whenever $\overline B(x, r) \subseteq D$;
--   - `DiskPshOn Ω q`, for a subset $\Omega$ of a complex normed space and a real function $q$, means that $q$ is upper semicontinuous on $\Omega$ and $q \circ \gamma$ is `DiskSubharmonicOn D` for every map $\gamma$ complex differentiable on an open $D \subseteq \mathbb C$ with $\gamma(D) \subseteq \Omega$ (plurisubharmonicity tested on holomorphic disks).
--
--   **Statement.** Let $V$ be a complex normed space that is locally compact (so finite-dimensional). Let $U \subseteq \mathbb C \times V$ be open, and let $q : \mathbb C \times V \to \mathbb R$ be continuous and nonnegative on $U$. Suppose $q$ is plurisubharmonic off the hyperplane $\{x_1 = 0\}$: `DiskPshOn (U ∩ {x | x.1 ≠ 0}) q`. Then `DiskPshOn U q`.
--
--   $$q \in C(U),\quad q \ge 0,\quad q \text{ plurisubharmonic on } U \setminus \{x_1 = 0\} \;\Longrightarrow\; q \text{ plurisubharmonic on } U.$$
--
--   This is a special case of the removable-singularities theorem for plurisubharmonic functions, which extends a plurisubharmonic function across a closed pluripolar set where it is locally bounded above (see Demailly, *Complex Analytic and Differential Geometry*, Chapter I, Theorem 5.24, cited by the paper). The paper uses it in Section 4 to extend the continuous trace across the branch locus.
--
--   Lean: `OAI.QuadricCounterexample.first_hyperplane_removable`, OpenAI's theorem of that name (in `lean/OAI/Geometry/QuadricBundles/Removability.lean`). The statement imports only the small definitions bundles `OAIQWQC000` and `OAIQWQC001` of this split (through `OAIQWQC001`). A definition of OpenAI's development needs it (through `rootTrace_psh`), so a later definitions bundle of this split imports this statement instead of proving it again.
-- source:
--   a special case of the removable-singularities theorem for plurisubharmonic functions (see J.-P. Demailly, Complex Analytic and Differential Geometry, Chapter I, Theorem 5.24); proof and Lean code: OpenAI, Ample rank-two bundles on the quadric surface without Griffiths-positive metrics, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 050; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/ample-rank-two-bundles-on-the-quadric-surface-without-griffiths-positive-metrics-September-24-2026/paper.pdf, Section 4; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/QuadricBundles/Removability.lean (declaration OAI.QuadricCounterexample.first_hyperplane_removable)

import Mathlib
import Definitions.Def_OAIQWQC001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 u16 u17 u18 u19 u20 u21 u22 u23 u24 u25 u26 u27 u28 u29

namespace QuadricCounterexample
open Set Filter Topology MeasureTheory Metric
open scoped unitInterval
noncomputable section

variable {V : Type u29} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [LocallyCompactSpace V]

theorem first_hyperplane_removable {U : Set (ℂ × V)} (hU : IsOpen U)
    {q : ℂ × V → ℝ} (hq : ContinuousOn q U) (hq0 : ∀ x ∈ U, 0 ≤ q x)
    (hp : DiskPshOn (U ∩ {x | x.1 ≠ 0}) q) : DiskPshOn U q := by
  sorry

end
end QuadricCounterexample

end OAI
end
