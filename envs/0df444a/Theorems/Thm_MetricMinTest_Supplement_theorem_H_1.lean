-- Prove2me | Theorems.Thm_MetricMinTest_Supplement_theorem_H_1
-- name    : MetricMinTest.Supplement.theorem_H_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:49:51.911912+00:00
-- url     : https://prove2.me/theorems/3db903ee-f701-4e78-a12b-f1233a154495
-- title:
--   Theorem H.1, p.30 — block law: testers with cost $5HL$ and budget $66H\ln(k/\delta)$, budget $840HL$; lower bound $D_\delta H/2\ge HL/8$
-- statement:
--   Let $\Pi$ partition $[k]$ into nonempty blocks $C$ of sizes $k_C$, with mean diameters $\Delta_C\ge0$ and margins $\gamma_C\in(0,1/4]$, and let $\delta\in(0,1/4]$, $L=\ln(1/\delta)$. The class requires $\max_{i\in C}\mu_i-\min_{i\in C}\mu_i\le\Delta_C$ for every block, without cross-block restrictions; a valid tester must reject when some mean is negative and accept when $\mu_i\ge\gamma_C$ for every $i\in C$ and every block $C$. Write $H=H(\Pi,\gamma,\Delta)=\sum_Ck_C/(\gamma_C^2+(k_C-1)(\gamma_C-\Delta_C)_+^2)$. Then
--
--   1. a valid tester has positive-input expected cost at most $5HL$ and budget at most $66H\ln(k/\delta)$;
--   2. another valid tester has budget $840HL$;
--   3. every valid tester has expected cost at least $D_\delta H/2\ge HL/8$ at the instance with common signed Bernoulli mean $\gamma_C$ within each block $C$, where $D_\delta=(1-2\delta)\ln((1-\delta)/\delta)$.
--
--   Known block structure is thus characterized up to constants by the closed-form workload $H(\Pi,\gamma,\Delta)$.
--
--   Differences from the source:
--   - encoding: a partition $\Pi$ of $[k]$ into blocks → the fibres of a surjective label $\mathrm{blk}:\iota\to\beta$ on a finite nonempty index type; reason: same partitions; blocks are nonempty
--   - encoding: standing $\delta\in(0,1/4]$ (§2) → hypothesis $\delta\in(0,1/4]$; reason: standing assumption
--   - encoding: validity with block-dependent margins → validity on the known-block class with rejection set "some mean negative" and acceptance set "$\mu_i\ge\gamma_C$ on every block", including measurability; reason: the contract of Definition 2.1 on this class
--   - encoding: budget → stopping time bounded for every private draw and every observation table; reason: definition of a deterministic budget
--   - encoding: expectations and probabilities → over private randomness times the observation table, in $[0,\infty]$; reason: published tester model
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), Appendix H and Theorem H.1, pp.29–30

import Mathlib
import Definitions.Def_MetricMinTest_IsViolating
import Definitions.Def_MetricMinTest_signedBernoulli
import Definitions.Def_MetricMinTest_Ddelta
import Definitions.Def_MetricMinTest_Supplement_IsValidOn
import Definitions.Def_MetricMinTest_Supplement_blockWorkload
import Definitions.Def_MetricMinTest_Supplement_InBlockClass
import Definitions.Def_MetricMinTest_Supplement_IsBlockPositive

namespace MetricMinTest.Supplement

open MeasureTheory

/-- **Theorem H.1 (Block law).** Chen–Fang, *Minimum-Mean Testing under Metric Constraints*, STOC 2027 submission (manuscript sha256 dcece193…ad32bb), Appendix H, pp.29–30: "Let Π partition [k] into blocks C,
with sizes k_C = |C|, mean diameters Δ_C ≥ 0, and margins γ_C ∈ (0, 1/4]. The class requires
max_{i∈C} µᵢ − min_{i∈C} µᵢ ≤ Δ_C (C ∈ Π), without cross-block restrictions. Validity is understood
with block-dependent margins: rejection is required when some mean is negative, and acceptance when
µᵢ ≥ γ_C for every i ∈ C and every block C. … Theorem H.1 (Block law). Writing H = H(Π, γ, Δ), a
valid tester has positive-input expected cost at most 5H ln(1/δ) and budget at most 66H ln(k/δ).
Another has budget 840H ln(1/δ). Every valid tester has expected cost at least D_δH/2 ≥ H ln(1/δ)/8
at the instance with common signed Bernoulli mean γ_C within each block C."

**Formalization Note.** The partition is the fibres of a surjective label `blk : ι → β` (nonempty
blocks); `k = |ι| ≥ 1`; standing `δ ∈ (0, 1/4]` (§2). Validity is `IsValidOn` with the class
`InBlockClass`, `neg` = some mean negative, `pos` = `IsBlockPositive`. "Positive-input expected
cost" is the supremum of `E_P τ` over positive instances of the class; a budget holds for every
private draw and every observation table. The first two bounds are for one tester. -/
theorem theorem_H_1 {ι β : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι] [Fintype β]
    [DecidableEq β] (blk : ι → β) (hblk : Function.Surjective blk) (γC ΔC : β → ℝ)
    (hγC : ∀ C, γC C ∈ Set.Ioc (0 : ℝ) (1 / 4)) (hΔC : ∀ C, 0 ≤ ΔC C) (δ : ℝ)
    (hδ : δ ∈ Set.Ioc (0 : ℝ) (1 / 4)) :
    (∃ T : Tester ι,
      IsValidOn T {P | InBlockClass blk ΔC P} {P | IsViolating P} {P | IsBlockPositive blk γC P} δ ∧
      (⨆ (P : Instance ι) (_ : InBlockClass blk ΔC P ∧ IsBlockPositive blk γC P),
        ∫⁻ p, ((T.stopTime p.1 p.2 : ℕ∞) : ENNReal) ∂(T.μξ.prod (streamLaw P))) ≤
        ENNReal.ofReal (5 * blockWorkload blk γC ΔC * Real.log (1 / δ)) ∧
      ∀ ξ ω, ((T.stopTime ξ ω : ℕ∞) : ENNReal) ≤
        ENNReal.ofReal (66 * blockWorkload blk γC ΔC * Real.log ((Fintype.card ι : ℝ) / δ))) ∧
    (∃ T : Tester ι,
      IsValidOn T {P | InBlockClass blk ΔC P} {P | IsViolating P} {P | IsBlockPositive blk γC P} δ ∧
      ∀ ξ ω, ((T.stopTime ξ ω : ℕ∞) : ENNReal) ≤
        ENNReal.ofReal (840 * blockWorkload blk γC ΔC * Real.log (1 / δ))) ∧
    (∀ T : Tester ι,
      IsValidOn T {P | InBlockClass blk ΔC P} {P | IsViolating P} {P | IsBlockPositive blk γC P} δ →
      ∀ P : Instance ι, (∀ i, P.law i = signedBernoulli (γC (blk i))) →
        ENNReal.ofReal (Ddelta δ * blockWorkload blk γC ΔC / 2) ≤
          ∫⁻ p, ((T.stopTime p.1 p.2 : ℕ∞) : ENNReal) ∂(T.μξ.prod (streamLaw P))) ∧
    blockWorkload blk γC ΔC * Real.log (1 / δ) / 8 ≤ Ddelta δ * blockWorkload blk γC ΔC / 2 := by sorry

end MetricMinTest.Supplement
