-- Prove2me | Theorems.Thm_OAI_QuadricCounterexample_log_norm_psh
-- name    : OAI.QuadricCounterexample.log_norm_psh
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T15:58:18.592538+00:00
-- url     : https://prove2.me/theorems/2faeea0b-a687-4c48-83e2-991235bbb34c
-- title:
--   The logarithm of the modulus of a nonvanishing holomorphic function is plurisubharmonic
-- statement:
--   The definitions are from the definitions bundles `OAIQWQC000` and `OAIQWQC001`:
--   - `DiskSubharmonicOn D u` (for $D \subseteq \mathbb C$) means that $u$ is upper semicontinuous on $D$ and satisfies the disk submean inequality $|B(x, r)|\,u(x) \le \int_{B(x,r)} u$ (with $u$ integrable on $B(x,r)$) whenever $\overline B(x, r) \subseteq D$;
--   - `DiskPshOn Ω q`, for a subset $\Omega$ of a complex normed space $E$ and $q : E \to \mathbb R$, means that $q$ is upper semicontinuous on $\Omega$ and that $q \circ \gamma$ is `DiskSubharmonicOn D` for every open $D \subseteq \mathbb C$ and every map $\gamma : \mathbb C \to E$ that is complex differentiable on $D$ with $\gamma(D) \subseteq \Omega$. This is plurisubharmonicity tested on holomorphic disks, for real-valued functions.
--
--   **Statement.** Let $E$ be a complex normed space, $U \subseteq E$ open, and $f : E \to \mathbb C$ complex differentiable on $U$ with $f(x) \ne 0$ for every $x \in U$. Then `DiskPshOn U (fun x ↦ Real.log ‖f x‖)`: the function $x \mapsto \log|f(x)|$ is plurisubharmonic on $U$.
--
--   $$f \text{ holomorphic and nowhere zero on } U \;\Longrightarrow\; \log|f| \text{ is plurisubharmonic on } U.$$
--
--   This is classical (see Demailly, *Complex Analytic and Differential Geometry*, Chapter I, §5); for nonvanishing $f$, $\log|f|$ is in fact pluriharmonic.
--
--   Lean: `OAI.QuadricCounterexample.log_norm_psh`, OpenAI's theorem of that name (in `lean/OAI/Geometry/QuadricBundles/Removability.lean`). The statement imports only the small definitions bundles `OAIQWQC000` and `OAIQWQC001` of this split (through `OAIQWQC001`).
-- source:
--   classical (log |f| is plurisubharmonic for holomorphic f; see J.-P. Demailly, Complex Analytic and Differential Geometry, Chapter I, §5); proof and Lean code: OpenAI, Ample rank-two bundles on the quadric surface without Griffiths-positive metrics, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 050; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/ample-rank-two-bundles-on-the-quadric-surface-without-griffiths-positive-metrics-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/QuadricBundles/Removability.lean (declaration OAI.QuadricCounterexample.log_norm_psh)

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

open scoped Pointwise
noncomputable section

attribute [local instance] Measure.Subtype.measureSpace

open Real

theorem log_norm_psh {E : Type u5} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {U : Set E} (_hU : IsOpen U) {f : E → ℂ} (hf : DifferentiableOn ℂ f U)
    (hn : ∀ x ∈ U, f x ≠ 0) : DiskPshOn U (fun x ↦ Real.log ‖f x‖) := by
  sorry

end
end QuadricCounterexample

end OAI
end
