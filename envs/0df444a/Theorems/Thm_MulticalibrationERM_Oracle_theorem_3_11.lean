-- Prove2me | Theorems.Thm_MulticalibrationERM_Oracle_theorem_3_11
-- name    : MulticalibrationERM.Oracle.theorem_3_11
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:51:12.521346+00:00
-- url     : https://prove2.me/theorems/7f7f9e63-8829-4dbe-a7ab-fee5c0df7803
-- title:
--   Theorem 3.11 — black-box ERM lower bound on the explicit hard family
-- statement:
--   There are absolute constants $c>0$ (sufficiently small) and $C>0$ (sufficiently large) such that the following holds. Let $\varepsilon>0$, $q\ge1$, $\beta=8\varepsilon$, $\kappa_{\mathrm{anc}}=2\lceil\log_2(1/\beta)\rceil+4$, $\Delta_c=128\kappa_{\mathrm{anc}}\beta$, $J=\lfloor1/(4\Delta_c)\rfloor$ (with $\Delta_c>0$, so that $J$ is defined), let $D\ge\max\{128,J,C\log(100q)\}$ be an integer, $X=[J]\times[D]$, $d_0=\lceil16D\log(8|X|)\rceil$, $t=\log(1000|X|)$, $A=\kappa_{\mathrm{anc}}^2+\log(1000q)$, and assume (3): $d_0\le|X|/2$, $|X|\ge C\kappa_{\mathrm{anc}}^2$, $\beta t\sqrt A\le c$. Then there is a family of instances, indexed by the hidden signs and the 16 planted block-sign vectors, each consisting of a class $H\subseteq\{-1,+1\}^X$ with $d_0\le\mathrm{VC}(H)\le24d_0$, a weighted ERM oracle for $H$ and a distribution over $X\times\{0,1\}$ with uniform input marginal, such that for every $q$-query black-box ERM learner using
--   $$n\le c\,\frac{|X|}{\beta^2A\,t}$$
--   labeled samples, some member of the family makes the learner's output $Q$ satisfy $\Pr\{\mathrm{MC}(Q)>\varepsilon\}\ge2/3$. Because the family is fixed before the learner, this holds even if the learner knows the input distribution, the bound $24d_0$, and every part of the instance except the hidden signs and the planted block signs.
--
--   Differences from the source:
--   - reading: 'this holds even if the learner knows the input distribution, the bound 24d_0 and every part of the instance except the hidden signs and the planted block signs' → ∃ a family of instances indexed by HiddenSigns J D (hidden signs and planted block signs), all with uniform marginal, binary outcomes and d_0 ≤ VC ≤ 24 d_0, chosen before n and the learner, ∀ learner ∃ index on which it fails; reason: a learner chosen after the family may depend on every public part of it; this implies the plain form ∀ learner ∃ H, oracle, D
--   - encoding: J = ⌊1/(4Δ_c)⌋ for every ε > 0 → the hypothesis 0 < Δ_c (lbDelta ε); reason: J is undefined when Δ_c = 0 (κ_anc = 0, i.e. ε ∈ [1/2, 1)); in Lean 1/0 = 0 would give J = 0, an empty X, and conditions (3) all true, so the hypothesis only excludes the undefined case
--   - encoding: X = [J] × [D] → Fin J × Fin D (0-based); reason: relabelling
--   - encoding: a q-query learner making at most q adaptive calls, outputting a finitely supported randomized predictor → exactly q queries (dummy queries allowed) and a finitely supported randomized predictor with values in [0,1] (measurable, automatic on the finite X); reason: a learner with fewer calls pads with dummy queries
--   - encoding: Pr{MC(Q) > ε} ≥ 2/3 → the outer measure of the failure event over samples, learner seed and oracle seeds is ≥ 2/3; reason: equal to the probability whenever the learner is measurable (the case the paper treats); for a non-measurable learner the paper's probability is not defined
--   - encoding: a distribution over X × {0,1} with uniform input marginal → D_X({x}) = 1/|X| for every x, and outcomes in {0,1} almost surely; reason: the definition of uniform marginal on a finite set
--   - encoding: auditors h : X → {−1,+1} → h : X → Bool with value pm (h x) ∈ {1, −1} (true ↦ +1); reason: relabelling of the two values; every auditor is an instance
-- source:
--   Okoroafor, The Sample Complexity of Multicalibration with an ERM Oracle, supplied 61-page preprint (PDF SHA256 654c7a8127547d76c5a4b6db236ce672c2c09a70d21d56a3981583e1805d0f8d; exact arXiv revision unresolved, not arXiv:2610.14363v1), p. 22, Theorem 3.11

import Mathlib
import Definitions.Def_NatureSLT_GrowthFunction_vcDim
import Definitions.Def_MulticalibrationERM_Oracle_Setting
import Definitions.Def_MulticalibrationERM_Oracle_ERM
import Definitions.Def_MulticalibrationERM_Oracle_BlackBox

open MeasureTheory ProbabilityTheory

namespace MulticalibrationERM.Oracle

/-- Theorem 3.11 (p. 22): black-box ERM lower bound. There are absolute constants `c > 0` (small)
and `C > 0` (large) such that the following holds. Let `ε > 0`, `q ≥ 1`, `β = 8ε`,
`κ_anc = 2⌈log₂(1/β)⌉ + 4`, `Δ_c = 128 κ_anc β`, `J = ⌊1/(4Δ_c)⌋`, an integer
`D ≥ max{128, J, C log(100q)}` (with `Δ_c > 0`, so that `J` is defined),
`X = [J] × [D]`, `d₀ = ⌈16 D log(8|X|)⌉`, `t = log(1000|X|)`,
`A = κ_anc² + log(1000q)`, and assume (3): `d₀ ≤ |X|/2`, `|X| ≥ C κ_anc²`, `β t √A ≤ c`.
Then for every `q`-query black-box ERM learner using `n ≤ c|X|/(β² A t)` labeled samples there
exist a class `H ⊆ {−1, +1}^X` with `d₀ ≤ VC(H) ≤ 24 d₀`, a weighted ERM oracle for `H`, and a
distribution over `X × {0, 1}` with uniform input marginal on which the learner's output `Q`
satisfies `Pr{MC(Q) > ε} ≥ 2/3`; this holds even if the learner knows the input distribution, the
bound `24 d₀`, and every part of the instance except the hidden signs and the planted block
signs. The last sentence is the quantifier order: the instance is a fixed function of the hidden
signs and planted block signs (`HiddenSigns J D`), chosen before the learner, and every member of
the family has the stated properties. -/
theorem theorem_3_11 :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧
    ∀ (ε : ℝ), 0 < ε → 0 < lbDelta ε → ∀ (q : ℕ), 1 ≤ q → ∀ (Dblk : ℕ),
      128 ≤ Dblk → lbJ ε ≤ Dblk → C * Real.log (100 * q) ≤ Dblk →
      (lbD0 ε Dblk : ℝ) ≤ ((lbJ ε * Dblk : ℕ) : ℝ) / 2 →
      C * lbKappa ε ^ 2 ≤ ((lbJ ε * Dblk : ℕ) : ℝ) →
      lbBeta ε * lbT ε Dblk * Real.sqrt (lbA ε q) ≤ c →
    ∃ (Ωo : Type) (_ : MeasurableSpace Ωo)
      (inst : HiddenSigns (lbJ ε) Dblk → BBInstance (Fin (lbJ ε) × Fin Dblk) Ωo),
      (∀ s, (lbD0 ε Dblk : ℕ∞) ≤ VC (inst s).H ∧ VC (inst s).H ≤ ((24 * lbD0 ε Dblk : ℕ) : ℕ∞) ∧
        (∀ x, (inst s).D.atom x = 1 / ((lbJ ε * Dblk : ℕ) : ℝ)) ∧
        ∀ᵐ z ∂(inst s).D.μ, z.2 = 0 ∨ z.2 = 1) ∧
      ∀ (n : ℕ), (n : ℝ) ≤ c * ((lbJ ε * Dblk : ℕ) : ℝ) /
          (lbBeta ε ^ 2 * lbA ε q * lbT ε Dblk) →
      ∀ {Ωl : Type} [MeasurableSpace Ωl] (μl : Measure Ωl) [IsProbabilityMeasure μl]
        (A : BBLearner (Fin (lbJ ε) × Fin Dblk) n q Ωl),
        ∃ s, (2 / 3 : ENNReal) ≤
          bbFailProb A μl (inst s).O (inst s).νo (inst s).D ε := by sorry

end MulticalibrationERM.Oracle
