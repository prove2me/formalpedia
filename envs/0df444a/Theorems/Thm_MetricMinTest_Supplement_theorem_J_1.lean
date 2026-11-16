-- Prove2me | Theorems.Thm_MetricMinTest_Supplement_theorem_J_1
-- name    : MetricMinTest.Supplement.theorem_J_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:51:41.258682+00:00
-- url     : https://prove2.me/theorems/42896084-2c2d-44d4-9e46-8fb1ab7a6e8c
-- title:
--   Theorem J.1, p.31 — two possible laws: every valid tester pays $\mathbb E_{P^\star}\tau\ge\frac3{32}k\gamma^{-2}L$, attained by an index-wise conjunction
-- statement:
--   Let $\mathcal P_2$ contain the instances on $k$ indices whose laws take at most two distinct values, with unknown assignment, and let $\gamma,\delta\in(0,1/4]$, $D_\delta=(1-2\delta)\ln((1-\delta)/\delta)$. At $P^\star$, where every law is signed Bernoulli of mean $\gamma$, every tester valid on $\mathcal P_2$ satisfies
--   $$\mathbb E_{P^\star}\tau\ge\frac{kD_\delta}{\gamma\ln((1+\gamma)/(1-\gamma))}\ge\frac{3kD_\delta}{8\gamma^2}\ge\frac3{32}k\gamma^{-2}\ln(1/\delta).$$
--   An index-wise conjunction attains the same order.
--
--   Realized homogeneity does not help: without a known constraint, the exceptional index can be anywhere and every index must be tested.
--
--   **Formalization Note** The index-wise conjunction tests every index in turn against threshold $0$ with gap $\gamma$, boundary $\ln(1/\delta)$ and cap $\lceil32\gamma^{-2}\ln(k/\delta)\rceil$ (Theorem H.1 with singleton blocks), in any fixed order; "attains the same order" is: it is valid on $\mathcal P_2$ with positive expected cost at most an absolute constant times $k\gamma^{-2}\ln(1/\delta)$.
--
--   Differences from the source:
--   - encoding: laws take at most two distinct values → there are laws $Q_1,Q_2$ with every $P_i\in\{Q_1,Q_2\}$; reason: same class
--   - encoding: standing $\gamma,\delta\in(0,1/4]$ and $k$ indices → hypotheses; finite nonempty index type; reason: standing assumptions
--   - encoding: valid tester on $\mathcal P_2$ → validity on $\mathcal P_2$ with rejection set "some mean negative" and acceptance set "every mean $\ge\gamma$", including measurability; reason: the contract of Definition 2.1 on this class
--   - reading: an index-wise conjunction attains the same order → the conjunction of the per-index tests (threshold $0$, gap $\gamma$, boundary $\ln(1/\delta)$, cap $\lceil32\gamma^{-2}\ln(k/\delta)\rceil$, any fixed order) is valid on $\mathcal P_2$ with positive expected cost $\le C\,k\gamma^{-2}\ln(1/\delta)$, $C$ absolute; reason: the construction of the proof (Theorem H.1 with singleton blocks); same order as the lower bound
--   - encoding: the cost measures and testers of §2 (sequential testers with private randomness; $C^\star$, $B^\star$, $C^{\mathrm{na}}$, $B^{\mathrm{na}}$) → the published tester model (stack-of-streams observations, validity including measurability of the acceptance event and the stopping time) and $[0,\infty]$-valued infima, suprema and expectations; reason: same quantities; probabilities and expectations require measurability, and the values can be infinite
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), Theorem J.1, p.31

import Mathlib
import Definitions.Def_MetricMinTest_IsViolating
import Definitions.Def_MetricMinTest_signedBernoulli
import Definitions.Def_MetricMinTest_Ddelta
import Definitions.Def_MetricMinTest_Supplement_IsValidOn
import Definitions.Def_MetricMinTest_Supplement_IsTwoLaw
import Definitions.Def_MetricMinTest_Supplement_seqTester

namespace MetricMinTest.Supplement

open MeasureTheory

/-- **Theorem J.1 (One realized type, two possible types).** Chen–Fang, *Minimum-Mean Testing under Metric Constraints*, STOC 2027 submission (manuscript sha256 dcece193…ad32bb), Theorem J.1, p.31: "Let P₂
contain instances whose laws take at most two distinct values, with unknown assignment. At P⋆ where
every law is signed Bernoulli of mean γ, every valid tester satisfies
E_{P⋆}τ ≥ kD_δ / (γ ln((1 + γ)/(1 − γ))) ≥ 3kD_δ/(8γ²) ≥ (3/32) kγ⁻² ln(1/δ). An index-wise
conjunction attains the same order."

**Formalization Note.** Standing `γ, δ ∈ (0, 1/4]` (§2), `k = |ι| ≥ 1`. Validity is the
Definition 2.1 contract on `P₂` (`IsValidOn` with class `IsTwoLaw`, `neg` = some mean negative,
`pos` = every mean `≥ γ`); no metric constraint. The index-wise conjunction is `seqTester` testing
every index in turn (any duplicate-free enumeration `ord`) against threshold `0` with gap `γ`,
boundary `ln(1/δ)` and cap `⌈32γ⁻² ln(k/δ)⌉` (Theorem H.1 with singleton blocks, the paper's
proof), accepting only if all pass. "Attains the same order": it is valid on `P₂` and its
supremum of `E_P τ` over positive instances of `P₂` is at most an absolute constant times
`kγ⁻² ln(1/δ)`. -/
theorem theorem_J_1 :
    ∃ C : ℝ, 0 < C ∧
      ∀ {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι] (γ δ : ℝ),
        γ ∈ Set.Ioc (0 : ℝ) (1 / 4) → δ ∈ Set.Ioc (0 : ℝ) (1 / 4) →
        (∀ T : Tester ι, IsValidOn T {P | IsTwoLaw P} {P | IsViolating P}
            {P | ∀ i, γ ≤ P.mean i} δ →
          ∀ P : Instance ι, (∀ i, P.law i = signedBernoulli γ) →
            ENNReal.ofReal ((Fintype.card ι : ℝ) * Ddelta δ /
                (γ * Real.log ((1 + γ) / (1 - γ)))) ≤
              ∫⁻ p, ((T.stopTime p.1 p.2 : ℕ∞) : ENNReal) ∂(T.μξ.prod (streamLaw P))) ∧
        3 * (Fintype.card ι : ℝ) * Ddelta δ / (8 * γ ^ 2) ≤
          (Fintype.card ι : ℝ) * Ddelta δ / (γ * Real.log ((1 + γ) / (1 - γ))) ∧
        3 / 32 * (Fintype.card ι : ℝ) * (γ ^ 2)⁻¹ * Real.log (1 / δ) ≤
          3 * (Fintype.card ι : ℝ) * Ddelta δ / (8 * γ ^ 2) ∧
        ∀ ord : List ι, ord.Nodup → (∀ i, i ∈ ord) →
          IsValidOn (seqTester (ord.map (fun i => (i, (0 : ℝ), γ, Real.log (1 / δ),
              ⌈32 * (γ ^ 2)⁻¹ * Real.log ((Fintype.card ι : ℝ) / δ)⌉₊))))
            {P | IsTwoLaw P} {P | IsViolating P} {P | ∀ i, γ ≤ P.mean i} δ ∧
          (⨆ (P : Instance ι) (_ : IsTwoLaw P ∧ ∀ i, γ ≤ P.mean i),
            ∫⁻ p, (((seqTester (ord.map (fun i => (i, (0 : ℝ), γ, Real.log (1 / δ),
                ⌈32 * (γ ^ 2)⁻¹ * Real.log ((Fintype.card ι : ℝ) / δ)⌉₊)))).stopTime
                  p.1 p.2 : ℕ∞) : ENNReal)
              ∂((seqTester (ord.map (fun i => (i, (0 : ℝ), γ, Real.log (1 / δ),
                ⌈32 * (γ ^ 2)⁻¹ * Real.log ((Fintype.card ι : ℝ) / δ)⌉₊)))).μξ.prod
                  (streamLaw P))) ≤
            ENNReal.ofReal (C * (Fintype.card ι : ℝ) * (γ ^ 2)⁻¹ * Real.log (1 / δ)) := by sorry

end MetricMinTest.Supplement
