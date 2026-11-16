-- Prove2me | Theorems.Thm_MetricMinTest_Supplement_theorem_7_5
-- name    : MetricMinTest.Supplement.theorem_7_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:45:30.536196+00:00
-- url     : https://prove2.me/theorems/2345a21f-9e35-425a-a0ee-94f322be01cb
-- title:
--   Theorem 7.5, p.18 — additivity of $J$ across components at mutual distance $\ge\gamma$
-- statement:
--   Let $d$ be a finite metric or pseudometric, $\gamma\in(0,1/4]$, and $[k]=V_1\sqcup\dots\sqcup V_s$ a partition into nonempty sets with $d(i,j)\ge\gamma$ whenever $i$ and $j$ belong to different sets. Writing $d_t$ for the restriction of $d$ to $V_t$,
--   $$J_d(\gamma)=\sum_{t=1}^sJ_{d_t}(\gamma).$$
--
--   Separated components can be screened independently without loss, which is what makes the regional workload computable on spaces glued from simpler pieces (Theorem 7.7).
--
--   **Formalization Note** The partition is given by a surjective label $\mathrm{blk}:[k]\to\beta$; $J_{d_t}$ is the mixed workload of the restricted metric, with its own admissible radii.
--
--   Differences from the source:
--   - encoding: standing assumptions of §2 (finite metric or pseudometric, $\gamma\in(0,1/4]$) → hypotheses ($d$ a pseudometric on a finite type, $\gamma\in(0,1/4]$); reason: standing assumptions; a metric is a pseudometric
--   - encoding: partition into nonempty sets $V_1,\dots,V_s$ → fibres of a surjective label $\mathrm{blk}:\iota\to\beta$, $\beta$ finite; reason: same partitions
--   - encoding: admissible regions $(Z,r)$, $r<\gamma$ an occurring distance → regions indexed by $(Z,(i_0,j_0))$ with radius $d(i_0,j_0)$; reason: every occurring distance is available; duplicated regions have equal cost, so $J$ is unchanged
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), Theorem 7.5, p.18

import Mathlib
import Definitions.Def_MetricMinTest_IsPseudometric
import Definitions.Def_MetricMinTest_Supplement_mixedWorkload

namespace MetricMinTest.Supplement

/-- **Theorem 7.5 (Additivity across separated components).** Chen–Fang, *Minimum-Mean Testing under Metric Constraints*, STOC 2027 submission (manuscript sha256 dcece193…ad32bb), Theorem 7.5, p.18: "Let
[k] = V₁ ⊔ ⋯ ⊔ V_s be a partition into nonempty sets, and suppose d(i, j) ≥ γ whenever i and j
belong to different sets. Writing d_t for the restriction of d to V_t, we have
J_d(γ) = ∑_{t=1}^s J_{d_t}(γ)."

**Formalization Note.** Standing setting (§2): `d` a pseudometric, `γ ∈ (0, 1/4]`. The partition is
the fibres of a surjective label `blk : ι → β` (nonempty parts); `d_t` is `d` restricted to the
subtype `{i // blk i = t}`, and `J_{d_t}` is its own mixed workload (its admissible radii are the
distances occurring in `d_t`). -/
theorem theorem_7_5 {ι β : Type} [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
    (d : ι → ι → ℝ) (hd : IsPseudometric d) (γ : ℝ) (hγ : γ ∈ Set.Ioc (0 : ℝ) (1 / 4))
    (blk : ι → β) (hblk : Function.Surjective blk)
    (hsep : ∀ i j, blk i ≠ blk j → γ ≤ d i j) :
    mixedWorkload d γ =
      ∑ t : β, mixedWorkload (fun i j : {x : ι // blk x = t} => d i j) γ := by sorry

end MetricMinTest.Supplement
