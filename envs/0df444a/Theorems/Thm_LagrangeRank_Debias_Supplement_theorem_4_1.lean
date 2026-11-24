-- Prove2me | Theorems.Thm_LagrangeRank_Debias_Supplement_theorem_4_1
-- name    : LagrangeRank.Debias.Supplement.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T03:53:35.710669+00:00
-- url     : https://prove2.me/theorems/1f723487-1606-4c03-9d38-2fbc271b9fd7
-- title:
--   Theorem 4.1 (corrected): asymptotic FWER control; counterexample to the printed familywise power claim
-- statement:
--   Fix $\kappa\ge1$, $c>0$ and $0<\alpha<1/2$. For a family $(R_i)_{i\in[n]}$ of ranking properties, the familywise procedure of Section 4.1 rejects $H_{0i}$ when every score vector in the box of half-width $C_M(\alpha,[n]\times[n])/\sqrt{npL}$ around the debiased estimator induces a ranking in $R_i$, where $C_M$ is the multiplier-bootstrap quantile (3.14) for the full pair set $[n]\times[n]$.
--
--   **FWER control (holds).** There is $C_0>0$ such that for all sequences $n,L\to\infty$ with $p\ge C_0\log n/n$ eventually, both rate conditions of Theorems 3.2 and 3.3, centered parameters of dynamic range at most $\kappa$, and every sequence of property families,
--   $$\mathrm{FWER}=P(\text{at least one Type I error})\le\alpha+o(1).$$
--
--   **Familywise power (refuted).** Use the complete-graph witness of Theorem 3.4: $n=t+4$, $L=n^{10}$, $p=1$, the centered scores $\theta^\pm$ with $\varepsilon=n^{-20}$, item 0 with the property excluding predecessor sets $\{2\}$ and $\{1,2,3\}$, every other item with the empty property. Under $\theta^+$ the only true alternative is item 0 and the signal (4.2) is $\Delta(\theta^+)=1$, eventually above every fixed multiple of $\sqrt{\log n/(npL)}$; under $\theta^-$ every hypothesis is null. At $\alpha=1/4$,
--   $$\neg\Big(\limsup\mathrm{FWER}_{\theta^-}\le\tfrac14\ \land\ P_{\theta^+}(\text{at least one Type II error})\to0\Big).$$
--   With the first part, the printed second clause of Theorem 4.1 fails on the full property domain.
--
--   This is the corrected form of Theorem 4.1: its FWER clause at full strength, and an explicit refutation of its power clause.
--
--   Differences from the source:
--   - correction: the clause: if Δ(θ*) ≳ √(log n/(npL)), P(at least one Type II error) → 0, for every family of Definition 2.3 properties → an explicit witness (one nontrivial property, all others empty, family signal 1) for which FWER control at α = 1/4 and vanishing familywise Type II error cannot hold together; with the first conjunct this refutes the power clause; reason: DISPROOF.md C3: the null and alternative data laws have total variation tending to zero
--   - reading: FWER ≤ α + o(1) → for every sequence of parameters and property families, the eventual bound FWER ≤ α + ε for each ε > 0; reason: o(1) is a vanishing sequence; the parameter and the properties may change with n
--   - encoding: sample size n and repeated-comparison count L tend to infinity → a separate sequence index t, dimensions n(t), L(t), and finite product probability spaces; reason: the law at each problem size is exactly (2.1); both graph and comparison randomness remain
--   - encoding: a family of ranking properties in the witness → one nontrivial property and empty properties for all other items; reason: empty properties are allowed by Definition 2.3; the family signal minimum is over the sole true alternative and equals 1, so no empty-minimum convention drives this counterexample
-- source:
--   Liu, Fang, Lu, Lagrangian Inference for Ranking Problems, arXiv:2110.00151v1, p. 26, Theorem 4.1; procedure p. 25

import Mathlib
import Definitions.Def_LagrangeRank_Debias_Supplement_Witnesses

namespace LagrangeRank.Debias.Supplement

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ENNReal
/-- Theorem 4.1 corrected: asymptotic FWER control holds for every 0 < α < 1/2; the clause
"no Type II error with probability → 1" is refuted by an explicit witness. -/
theorem theorem_4_1 (κ c α : ℝ) (hκ : 1 ≤ κ) (hc : 0 < c) (hα : 0 < α ∧ α < 1/2) :
    (∃ C0 : ℝ, 0 < C0 ∧
      ∀ (n L : ℕ → ℕ) (p : ℕ → unitInterval) (θ : (t : ℕ) → Vec (n t))
        (R : (t : ℕ) → Fin (n t) → Set (Ranking (n t))),
        Regime n L p → Density C0 n p → Rates32 n L p → Rates33 n L p →
        (∀ t, Parameter κ (θ t)) → (∀ t i, RankingProperty i (R t i)) →
        AsymptoticUpper (fun t => fwer (L := L t) (p t) c α (θ t) (R t)) α) ∧
    (Regime witnessN witnessL (fun _ => 1) ∧
    Rates32 witnessN witnessL (fun _ => 1) ∧ Rates33 witnessN witnessL (fun _ => 1) ∧
    (∀ C0 : ℝ, Density C0 witnessN (fun _ => 1)) ∧
    (∀ t, Parameter (Real.exp 4) (nearScores t true) ∧
      Parameter (Real.exp 4) (nearScores t false) ∧
      (∀ i, RankingProperty i (witnessFamily t i)) ∧
      familySignal (nearScores t true) (witnessFamily t) = 1) ∧
    (∀ C : ℝ, 0 < C → ∀ᶠ t in atTop,
      ENNReal.ofReal (C * signalScale (witnessN t) (witnessL t) 1) <
        familySignal (nearScores t true) (witnessFamily t)) ∧
    ¬(AsymptoticUpper (fun t => fwer (L := witnessL t) 1 1 (1/4)
          (nearScores t false) (witnessFamily t)) (1/4) ∧
       Tendsto (fun t => familyTypeII (L := witnessL t) 1 1 (1/4)
          (nearScores t true) (witnessFamily t)) atTop (𝓝 0))) := by sorry

end LagrangeRank.Debias.Supplement
