-- Prove2me | Theorems.Thm_MetricMinTest_Supplement_theorem_K_3
-- name    : MetricMinTest.Supplement.theorem_K_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:53:21.828194+00:00
-- url     : https://prove2.me/theorems/4c3073e8-18ab-4cc9-9155-8db4ceeef122
-- title:
--   Theorem K.3, p.33 — superharmonic chains: $C^\star_\Gamma$ and $B^\star_\Gamma$ are $\Theta(|V_\partial|\gamma^{-2}\ln(1/\delta))$, with constants $15/16$, $3200$, $400$
-- statement:
--   Let $V^\circ=I\sqcup V_\partial$ be a finite vertex set with nonempty boundary $V_\partial$, and $\Gamma$ a known transition matrix making $V_\partial$ absorbing, whose chain reaches $V_\partial$ almost surely from every state. Every vertex has a law on $[-1,1]$ and may be sampled, and the means satisfy the superharmonic constraint $\mu_v\ge\sum_w\Gamma_{vw}\mu_w$ for $v\in I$. The testing contract is unchanged (reject if some mean is negative, accept if every mean is at least $\gamma$), with complexity measures $C^\star_\Gamma$, $B^\star_\Gamma$. For every such chain and $\gamma,\delta\in(0,1/4]$,
--   $$\frac{15}{16}|V_\partial|\gamma^{-2}D_\delta\le C^\star_\Gamma\le B^\star_\Gamma\le3200\,|V_\partial|\gamma^{-2}\ln(1/\delta),$$
--   and the expected-cost upper bound $C^\star_\Gamma\le400\,|V_\partial|\gamma^{-2}\ln(1/\delta)$ also holds.
--
--   The complexity is therefore $\Theta(|V_\partial|\gamma^{-2}\ln(1/\delta))$, even though all interior vertices may be queried: the boundary is the exact sampling dimension.
--
--   Differences from the source:
--   - encoding: the chain reaches $V_\partial$ almost surely from every state → $\sum_{b\in V_\partial}(\Gamma^n)_{vb}\to1$ for every $v$; reason: with $V_\partial$ absorbing this sum is the probability of having hit $V_\partial$ by time $n$
--   - encoding: transition matrix → nonnegative entries and unit row sums; reason: definition
--   - encoding: $C^\star_\Gamma$, $B^\star_\Gamma$ → $C^\star$, $B^\star$ on the superharmonic class with rejection set "some mean negative" and acceptance set "every mean $\ge\gamma$"; reason: "the testing contract is unchanged"
--   - encoding: the cost measures and testers of §2 (sequential testers with private randomness; $C^\star$, $B^\star$, $C^{\mathrm{na}}$, $B^{\mathrm{na}}$) → the published tester model (stack-of-streams observations, validity including measurability of the acceptance event and the stopping time) and $[0,\infty]$-valued infima, suprema and expectations; reason: same quantities; probabilities and expectations require measurability, and the values can be infinite
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), §K.1 and Theorem K.3, pp.32–33

import Mathlib
import Definitions.Def_MetricMinTest_IsViolating
import Definitions.Def_MetricMinTest_Ddelta
import Definitions.Def_MetricMinTest_Supplement_CstarOn
import Definitions.Def_MetricMinTest_Supplement_BstarOn
import Definitions.Def_MetricMinTest_Supplement_IsAbsorbingChain
import Definitions.Def_MetricMinTest_Supplement_IsSuperharmonic

namespace MetricMinTest.Supplement

/-- **Theorem K.3 (The boundary is the exact sampling dimension).** Chen–Fang, *Minimum-Mean Testing under Metric Constraints*, STOC 2027 submission (manuscript sha256 dcece193…ad32bb), §K.1 and Theorem K.3,
pp.32–33: "Let V° = I ⊔ V∂ be a finite vertex set with nonempty boundary V∂. A known transition
matrix Γ makes V∂ absorbing; its chain (Z_t) reaches V∂ almost surely from every state. Every vertex
has a law on [−1, 1] and may be sampled. Instead of pairwise Lipschitz constraints, assume
µ_v ≥ ∑_{w∈V°} Γ_vw µ_w (v ∈ I). (K.1) The testing contract is unchanged. Write C⋆_Γ, B⋆_Γ for its
complexity measures. Theorem K.3. For every such chain and γ, δ ∈ (0, 1/4],
(15/16)|V∂|γ⁻²D_δ ≤ C⋆_Γ ≤ B⋆_Γ ≤ 3200|V∂|γ⁻² ln(1/δ). An expected-cost upper bound
400|V∂|γ⁻² ln(1/δ) also holds."

**Formalization Note.** `IsAbsorbingChain Γ bd` (nonnegative unit-row-sum matrix, `Γ_bb = 1` on
`bd = V∂ ≠ ∅`, reaching `V∂` with probability tending to one). The class is `IsSuperharmonic`
(K.1); the contract is Definition 2.1's: `neg` = some mean negative, `pos` = every mean `≥ γ`.
`C⋆_Γ = CstarOn`, `B⋆_Γ = BstarOn` for this class. All vertices, interior included, may be
queried. -/
theorem theorem_K_3 {V : Type} [Fintype V] [DecidableEq V] (Γ : Matrix V V ℝ) (bd : Finset V)
    (hΓ : IsAbsorbingChain Γ bd) (γ δ : ℝ) (hγ : γ ∈ Set.Ioc (0 : ℝ) (1 / 4))
    (hδ : δ ∈ Set.Ioc (0 : ℝ) (1 / 4)) :
    ENNReal.ofReal (15 / 16 * (bd.card : ℝ) * (γ ^ 2)⁻¹ * Ddelta δ) ≤
      CstarOn {P | IsSuperharmonic Γ bd P} {P | IsViolating P} {P | ∀ v, γ ≤ P.mean v} δ ∧
    CstarOn {P | IsSuperharmonic Γ bd P} {P | IsViolating P} {P | ∀ v, γ ≤ P.mean v} δ ≤
      BstarOn {P | IsSuperharmonic Γ bd P} {P | IsViolating P} {P | ∀ v, γ ≤ P.mean v} δ ∧
    BstarOn {P | IsSuperharmonic Γ bd P} {P | IsViolating P} {P | ∀ v, γ ≤ P.mean v} δ ≤
      ENNReal.ofReal (3200 * (bd.card : ℝ) * (γ ^ 2)⁻¹ * Real.log (1 / δ)) ∧
    CstarOn {P | IsSuperharmonic Γ bd P} {P | IsViolating P} {P | ∀ v, γ ≤ P.mean v} δ ≤
      ENNReal.ofReal (400 * (bd.card : ℝ) * (γ ^ 2)⁻¹ * Real.log (1 / δ)) := by sorry

end MetricMinTest.Supplement
