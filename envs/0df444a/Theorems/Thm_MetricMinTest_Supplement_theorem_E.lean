-- Prove2me | Theorems.Thm_MetricMinTest_Supplement_theorem_E
-- name    : MetricMinTest.Supplement.theorem_E
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:41:56.813209+00:00
-- url     : https://prove2.me/theorems/a9482b8e-8142-407e-a056-ece932dc492d
-- title:
--   Theorem E, p.3 — structure of the regional workload $J$: $H\le J\le F$, $B^\star=O(JL)$, additivity, $J=\min\{F,H(1+\ln D)\}$ on homogeneous metrics, $J_{d_m}=H_{d_m}(1+\ln(1+3m/4))$
-- statement:
--   Let $J=J_d(\gamma)$ be the mixed workload (7.1). For every finite metric or pseudometric and $\gamma,\delta\in(0,1/4]$, with $L=\ln(1/\delta)$,
--   $$H\le J\le F,\qquad B^\star_d(\gamma,\delta)=O(JL).$$
--   1. $J$ is additive over components at mutual distance at least $\gamma$: if $[k]=V_1\sqcup\dots\sqcup V_s$ with nonempty parts and $d(i,j)\ge\gamma$ across parts, then $J_d(\gamma)=\sum_tJ_{d_t}(\gamma)$, $d_t$ the restriction of $d$ to $V_t$.
--   2. If $d$ is a vertex-transitive metric whose distinct points are at distance at least $\gamma/2$, then
--   $$J=\min\{F,\ H(1+\ln D)\},\qquad D=\gamma^{-2}\sum_j(\gamma-d(i,j))_+^2 .$$
--   3. In particular $J_{d_m}=H_{d_m}(1+\ln(1+3m/4))$ for every $m\ge1$.
--   4. There are metrics with $J=\Theta(H\log\log k)$ for which both $F$ and the best single-cover screening expression $\inf_{(Z,r):S(Z,r)=[k]}H_{Z,r}(1+\ln\rho_{Z,r})$ have order $H\log k$.
--
--   Regional composition therefore gives a general adaptive upper bound between the information and certificate workloads, computable exactly on symmetric and separated spaces.
--
--   **Formalization Note** Item 4 is a family statement with absolute constants: for every $\gamma\in(0,1/4]$ and every $N$ there is a metric on $k\ge N$ points with the stated orders.
--
--   Differences from the source:
--   - encoding: a finite metric or pseudometric on $[k]$ → a pseudometric on a finite nonempty index type ($k=|\iota|\ge1$); reason: a metric is a pseudometric; $[k]$ has $k\ge1$ points
--   - encoding: $O(JL)$, $\Theta(H\log\log k)$ and "order $H\log k$" → explicit constants $c,C>0$ quantified before every variable they must not depend on; reason: the paper's convention for $\asymp$, $O$, $\Theta$, $\Omega$ (§2, p.6)
--   - encoding: admissible regions $(Z,r)$, $r<\gamma$ an occurring distance → regions indexed by $(Z,(i_0,j_0))$ with radius $d(i_0,j_0)$; reason: every occurring distance is available; duplicated regions have equal cost, so $J$ is unchanged
--   - encoding: additive over components at mutual distance at least $\gamma$ → the statement of Theorem 7.5 (partition by a surjective label into nonempty parts, cross distances $\ge\gamma$, $J$ of each restricted metric); reason: the paper proves the clause as Theorem 7.5
--   - encoding: vertex-transitive metric → a metric (pseudometric with $d(i,j)=0\Rightarrow i=j$) with transitive isometry group, $D$ computed at an arbitrary point $i$; reason: vertex-transitivity is transitivity of the isometry group (Theorem 7.4)
--   - reading: there are metrics with $J=\Theta(H\log\log k)$ for which $F$ and the best single cover have order $H\log k$ → absolute $c,C>0$ such that for every $\gamma\in(0,1/4]$ and every $N$ some metric on $k\ge N$ points has $cH\ln\ln k\le J\le CH\ln\ln k$ and $cH\ln k\le F,\Sigma\le CH\ln k$; reason: $\Theta$ and order are asymptotic statements about a family with $k\to\infty$
--   - encoding: the cost measures and testers of §2 (sequential testers with private randomness; $C^\star$, $B^\star$, $C^{\mathrm{na}}$, $B^{\mathrm{na}}$) → the published tester model (stack-of-streams observations, validity including measurability of the acceptance event and the stopping time) and $[0,\infty]$-valued infima, suprema and expectations; reason: same quantities; probabilities and expectations require measurability, and the values can be infinite
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), Theorem E, p.3

import Mathlib
import Definitions.Def_MetricMinTest_IsPseudometric
import Definitions.Def_MetricMinTest_dm
import Definitions.Def_MetricMinTest_infoWorkload
import Definitions.Def_MetricMinTest_certWorkload
import Definitions.Def_MetricMinTest_Bstar
import Definitions.Def_MetricMinTest_Supplement_mixedWorkload
import Definitions.Def_MetricMinTest_Supplement_singleCoverInf

namespace MetricMinTest.Supplement

/-- **Theorem E (Structure of the regional workload).** Chen–Fang, *Minimum-Mean Testing under Metric Constraints*, STOC 2027 submission (manuscript sha256 dcece193…ad32bb), Theorem E, p.3: "For every finite
metric or pseudometric and γ, δ ∈ (0, 1/4], H ≤ J ≤ F and B⋆_d(γ, δ) = O(JL). The workload J is
additive over components at mutual distance at least γ. If d is a vertex-transitive metric whose
distinct points are at distance at least γ/2, then J = min{F, H(1 + ln D)},
D = γ⁻² ∑_j (γ − d(i, j))₊². In particular, J_{d_m} = H_{d_m}(1 + ln(1 + 3m/4)). There are metrics
with J = Θ(H log log k) for which both F and the best single-cover screening expression have order
H log k."

**Formalization Note.** `J = mixedWorkload`; the `O` and the `Θ`/order statements use absolute
constants chosen before the metric and `γ`. Additivity is Theorem 7.5's statement (partition into
nonempty parts given by a surjective label, cross distances `≥ γ`, `J` of each part of the
restricted metric). Vertex-transitive: transitive isometry group (as in Theorem 7.4); the formula
holds with `D` computed at any point `i`. The last sentence is a family statement: for every
`γ ∈ (0, 1/4]` and every `N` there is a metric on `k ≥ N` points with `J` between `cH ln ln k`
and `CH ln ln k`, and `F` and the best single-cover expression `singleCoverInf d γ 1` both between
`cH ln k` and `CH ln k`. -/
theorem theorem_E :
    ∃ C₁ c C : ℝ, 0 < C₁ ∧ 0 < c ∧ 0 < C ∧
      (∀ {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι] (d : ι → ι → ℝ), IsPseudometric d →
        ∀ γ δ : ℝ, γ ∈ Set.Ioc (0 : ℝ) (1 / 4) → δ ∈ Set.Ioc (0 : ℝ) (1 / 4) →
          infoWorkload d γ ≤ mixedWorkload d γ ∧ mixedWorkload d γ ≤ certWorkload d γ ∧
          Bstar d γ δ ≤ ENNReal.ofReal (C₁ * mixedWorkload d γ * Real.log (1 / δ))) ∧
      (∀ {ι β : Type} [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β] (d : ι → ι → ℝ),
        IsPseudometric d → ∀ γ : ℝ, γ ∈ Set.Ioc (0 : ℝ) (1 / 4) →
        ∀ blk : ι → β, Function.Surjective blk → (∀ i j, blk i ≠ blk j → γ ≤ d i j) →
          mixedWorkload d γ =
            ∑ t : β, mixedWorkload (fun i j : {x : ι // blk x = t} => d i j) γ) ∧
      (∀ {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι] (d : ι → ι → ℝ), IsPseudometric d →
        (∀ i j, d i j = 0 → i = j) →
        (∀ i i' : ι, ∃ σ : ι ≃ ι, (∀ x y, d (σ x) (σ y) = d x y) ∧ σ i = i') →
        ∀ γ : ℝ, γ ∈ Set.Ioc (0 : ℝ) (1 / 4) → (∀ i j, i ≠ j → γ / 2 ≤ d i j) →
        ∀ i, mixedWorkload d γ = min (certWorkload d γ)
          (infoWorkload d γ * (1 + Real.log ((γ ^ 2)⁻¹ * ∑ j, (max (γ - d i j) 0) ^ 2)))) ∧
      (∀ m : ℕ, 1 ≤ m → ∀ γ : ℝ, γ ∈ Set.Ioc (0 : ℝ) (1 / 4) →
        mixedWorkload (dm m γ) γ = infoWorkload (dm m γ) γ * (1 + Real.log (1 + 3 * (m : ℝ) / 4))) ∧
      (∀ γ : ℝ, γ ∈ Set.Ioc (0 : ℝ) (1 / 4) → ∀ N : ℕ, ∃ k : ℕ, N ≤ k ∧
        ∃ d : Fin k → Fin k → ℝ, IsPseudometric d ∧ (∀ i j, d i j = 0 → i = j) ∧
          c * (infoWorkload d γ * Real.log (Real.log k)) ≤ mixedWorkload d γ ∧
          mixedWorkload d γ ≤ C * (infoWorkload d γ * Real.log (Real.log k)) ∧
          c * (infoWorkload d γ * Real.log k) ≤ certWorkload d γ ∧
          certWorkload d γ ≤ C * (infoWorkload d γ * Real.log k) ∧
          c * (infoWorkload d γ * Real.log k) ≤ singleCoverInf d γ 1 ∧
          singleCoverInf d γ 1 ≤ C * (infoWorkload d γ * Real.log k)) := by sorry

end MetricMinTest.Supplement
