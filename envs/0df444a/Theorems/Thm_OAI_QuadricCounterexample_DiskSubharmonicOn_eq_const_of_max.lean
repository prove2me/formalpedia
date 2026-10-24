-- Prove2me | Theorems.Thm_OAI_QuadricCounterexample_DiskSubharmonicOn_eq_const_of_max
-- name    : OAI.QuadricCounterexample.DiskSubharmonicOn.eq_const_of_max
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T15:57:25.369985+00:00
-- url     : https://prove2.me/theorems/8705474e-aa32-45bc-afd8-5cd704a5551e
-- title:
--   Strong maximum principle for subharmonic functions in the plane: a disk-submean function on a connected open set that attains its maximum is constant
-- statement:
--   The definition `DiskSubharmonicOn` is from the definitions bundle `OAIQWQC000`. For an open set $\Omega \subseteq \mathbb C$ and $u : \mathbb C \to \mathbb R$, `DiskSubharmonicOn Ω u` means that $u$ is upper semicontinuous on $\Omega$ (`UpperSemicontinuousOn u Ω`) and satisfies the disk submean inequality: for every $x \in \Omega$ and $r > 0$ with $\overline B(x, r) \subseteq \Omega$, $u$ is integrable on $B(x, r)$ and
--   $$|B(x, r)|\; u(x) \;\le\; \int_{B(x,r)} u(y)\, dy$$
--   (Lebesgue measure on $\mathbb C$). This is the usual notion of a subharmonic function with values in $\mathbb R$.
--
--   **Statement.** Let $\Omega \subseteq \mathbb C$ be open and preconnected (`IsPreconnected Ω`), let `DiskSubharmonicOn Ω u`, and let $x \in \Omega$ with $u(y) \le u(x)$ for all $y \in \Omega$. Then $u(y) = u(x)$ for every $y \in \Omega$.
--
--   $$u \text{ subharmonic on a connected open } \Omega,\quad u \le u(x) \text{ on } \Omega \text{ for some } x \in \Omega \;\Longrightarrow\; u \equiv u(x) \text{ on } \Omega.$$
--
--   This is the strong maximum principle for subharmonic functions (classical; see Ransford, *Potential Theory in the Complex Plane*, Section 2.3).
--
--   Lean: `OAI.QuadricCounterexample.DiskSubharmonicOn.eq_const_of_max`, OpenAI's theorem of that name (in `lean/OAI/Geometry/QuadricBundles/Removability.lean`). The statement imports only the small definitions bundle `OAIQWQC000` of this split. On this platform, `HunterPDE.Harmonic.strong_maximum_principle` (6c90159c) is the same principle for $C^2$ functions with $\Delta u \ge 0$ on $\mathbb R^n$; this statement needs no differentiability.
-- source:
--   classical (the strong maximum principle for subharmonic functions; see T. Ransford, Potential Theory in the Complex Plane, Cambridge University Press, 1995, Section 2.3); proof and Lean code: OpenAI, Ample rank-two bundles on the quadric surface without Griffiths-positive metrics, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 050; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/ample-rank-two-bundles-on-the-quadric-surface-without-griffiths-positive-metrics-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/QuadricBundles/Removability.lean (declaration OAI.QuadricCounterexample.DiskSubharmonicOn.eq_const_of_max)

import Mathlib
import Definitions.Def_OAIQWQC000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 u16 u17 u18 u19 u20 u21 u22 u23 u24 u25 u26 u27 u28 u29

namespace QuadricCounterexample
open Set Filter Topology MeasureTheory Metric

theorem DiskSubharmonicOn.eq_const_of_max {Ω : Set ℂ} {u : ℂ → ℝ}
    (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω) (hu : DiskSubharmonicOn Ω u)
    {x : ℂ} (hx : x ∈ Ω) (hmax : ∀ y ∈ Ω, u y ≤ u x) :
    ∀ y ∈ Ω, u y = u x := by
  sorry

open scoped Pointwise
end QuadricCounterexample

end OAI
end
