-- Prove2me | Theorems.Thm_MetricMinTest_Supplement_theorem_6_1
-- name    : MetricMinTest.Supplement.theorem_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:43:25.670345+00:00
-- url     : https://prove2.me/theorems/0436438b-7388-45da-b174-6291ca34f75c
-- title:
--   Theorem 6.1, p.14 — distance-profile bridge: $H\le F\le s_dH$, covers and allocations convert, $s_j\le q_j$, $s_j\le1+2\ln(a_{j1}/a_{jq_j})$
-- statement:
--   For each center $j$ let $0=r_{j1}<\dots<r_{jq_j}<\gamma$ be the distinct distances from $j$ below $\gamma$, $a_{j\ell}=\gamma-r_{j\ell}$, $a_{j,q_j+1}=0$, and
--   $$s_j=\sum_{\ell=1}^{q_j}\Big(1-\frac{a_{j,\ell+1}^2}{a_{j\ell}^2}\Big),\qquad s_d=\max_js_j .$$
--   Then
--   $$H_d(\gamma)\le F_d(\gamma)\le s_d\,H_d(\gamma).$$
--   Moreover every fractional ball cover $y$ induces a feasible allocation for (1.1) of mass $C(y)$; every feasible allocation $w$ induces a fractional ball cover of cost $\sum_jw_js_j$. Finally $s_j\le q_j$ and $s_j\le1+2\ln(a_{j1}/a_{jq_j})$.
--
--   The distance profile $s_d$ measures exactly how much is lost by replacing shared information by local threshold certificates; it is the bridge behind Theorem D.
--
--   **Formalization Note** Standing setting: $d$ a pseudometric on a finite nonempty index set, $\gamma\in(0,1/4]$. Here $a_{j1}=\gamma$, and $a_{jq_j}=\gamma-\max\{d(j,i):d(j,i)<\gamma\}$.
--
--   Differences from the source:
--   - encoding: standing assumptions of §2 (finite metric or pseudometric, $\gamma\in(0,1/4]$) → hypotheses of the statement; reason: standing assumptions of the section
--   - generalization: "a cover $y$ induces a feasible allocation of mass $C(y)$", for covers over the indexed balls $B_{j\ell}$ (distinct distances) → "a cover $y$ induces a feasible allocation of mass $C(y)$", for covers in the pair encoding of the published certificate workload (a pair $(j,i)$ with $d(j,i)<\gamma$ is the ball $B(j,d(j,i))$; a repeated distance duplicates a ball); reason: a cover over distinct balls is the special case supported on one pair per ball, so the statement specializes to the source's
--   - encoding: an allocation $w$ induces a cover of cost $\sum_jw_js_j$ → existence of a fractional cover in the pair encoding with cost exactly $\sum_jw_js_j$; reason: the pair encoding realizes every cover over distinct balls at the same cost
--   - encoding: $q_j$, $a_{j1}$, $a_{jq_j}$ → the number of distinct distances below $\gamma$ from $j$, $\gamma$, and $\gamma$ minus the supremum of those distances; reason: same values ($r_{j1}=d(j,j)=0$; the set is finite and nonempty)
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), Theorem 6.1, p.14

import Mathlib
import Definitions.Def_MetricMinTest_IsPseudometric
import Definitions.Def_MetricMinTest_infoWorkload
import Definitions.Def_MetricMinTest_certWorkload
import Definitions.Def_MetricMinTest_centerProfile
import Definitions.Def_MetricMinTest_distProfile
import Definitions.Def_MetricMinTest_Supplement_IsBallCover
import Definitions.Def_MetricMinTest_Supplement_ballCoverCost

namespace MetricMinTest.Supplement

/-- **Theorem 6.1 (Distance-profile bridge).** Chen–Fang, *Minimum-Mean Testing under Metric Constraints*, STOC 2027 submission (manuscript sha256 dcece193…ad32bb), Theorem 6.1, p.14: "Let
s_j = ∑_{ℓ=1}^{q_j} (1 − a²_{j,ℓ+1}/a²_{jℓ}) and s_d = max_j s_j. Then
H_d(γ) ≤ F_d(γ) ≤ s_d H_d(γ). A cover y induces a feasible allocation of mass C(y); an allocation
w induces a cover of cost ∑_j w_j s_j. Also s_j ≤ q_j and s_j ≤ 1 + 2 ln(a_{j1}/a_{jq_j})."

**Formalization Note.** Standing setting (§2, p.6): `d` a pseudometric on a finite nonempty index
type, `γ ∈ (0, 1/4]`. `s_j` and `s_d` are the published `centerProfile` and `distProfile`.
`q_j` is the number of distinct distances `d j i < γ`; `a_{j1} = γ − r_{j1} = γ` (`r_{j1} = 0`) and
`a_{jq_j} = γ − r_{jq_j}` with `r_{jq_j}` the largest distance from `j` below `γ` (`sSup` of that
finite nonempty set). Covers and their cost `C(y)` are in the indexed-ball encoding of the
published `certWorkload` (`IsBallCover`, `ballCoverCost`); an allocation is a feasible point of
(1.1). "Induces" is existence of the object with the stated mass or cost. -/
theorem theorem_6_1 {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι] (d : ι → ι → ℝ)
    (hd : IsPseudometric d) (γ : ℝ) (hγ : γ ∈ Set.Ioc (0 : ℝ) (1 / 4)) :
    infoWorkload d γ ≤ certWorkload d γ ∧
    certWorkload d γ ≤ distProfile d γ * infoWorkload d γ ∧
    (∀ y : ι × ι → ℝ, IsBallCover d γ y →
      ∃ w : ι → ℝ, (∀ j, 0 ≤ w j) ∧ (∀ i, 1 ≤ ∑ j, w j * (max (γ - d i j) 0) ^ 2) ∧
        ∑ j, w j = ballCoverCost d γ y) ∧
    (∀ w : ι → ℝ, (∀ j, 0 ≤ w j) → (∀ i, 1 ≤ ∑ j, w j * (max (γ - d i j) 0) ^ 2) →
      ∃ y : ι × ι → ℝ, IsBallCover d γ y ∧ ballCoverCost d γ y = ∑ j, w j * centerProfile d γ j) ∧
    (∀ j, centerProfile d γ j ≤
      (((Finset.univ.image (fun i => d j i)).filter (· < γ)).card : ℝ)) ∧
    (∀ j, centerProfile d γ j ≤ 1 + 2 * Real.log (γ /
      (γ - sSup (((Finset.univ.image (fun i => d j i)).filter (· < γ) : Finset ℝ) : Set ℝ)))) := by sorry

end MetricMinTest.Supplement
