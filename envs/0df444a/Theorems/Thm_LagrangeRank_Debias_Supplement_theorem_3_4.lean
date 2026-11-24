-- Prove2me | Theorems.Thm_LagrangeRank_Debias_Supplement_theorem_3_4
-- name    : LagrangeRank.Debias.Supplement.theorem_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T03:52:12.421801+00:00
-- url     : https://prove2.me/theorems/ad9b0d37-832e-41eb-bfdc-b3de3976a514
-- title:
--   Theorem 3.4 (corrected): uniform Type I control of the general test; counterexample to the printed power claim
-- statement:
--   Fix a bounded dynamic range $\kappa\ge1$, the ridge coefficient $c>0$ of $\lambda_0=c\sqrt{np\log n/L}$, and a level $\alpha\in(0,1)$. The general testing procedure for item $i$ and a ranking property $R_i$ (Definition 2.3) rejects $H_0:\gamma^*\notin R_i$ when every score vector in the box (3.15), with half-width $c_W(\alpha,i)/\sqrt{npL}$ around the debiased estimator, induces a ranking in $R_i$; $c_W(\alpha,i)$ is the multiplier-bootstrap quantile (3.14) for the star set $\{(i,j):j\ne i\}$.
--
--   **Type I control (holds).** There is $C_0>0$ such that for all sequences $n,L\to\infty$ with $p\ge C_0\log n/n$ eventually, both rate conditions of Theorems 3.2 and 3.3, centered parameters of dynamic range at most $\kappa$, and every sequence of items, properties and null parameters ($\gamma(\theta^*)\notin R_i$),
--   $$\limsup_{t\to\infty} P_{\theta^*}(\text{reject }H_0)\le\alpha .$$
--
--   **Power (refuted).** Take $n=t+4$, $L=n^{10}$, $p=1$, and center
--   $$\theta^+=(0,\varepsilon,-\varepsilon,-1,-2,\ldots,-2),\quad \theta^-=(0,-\varepsilon,\varepsilon,-1,-2,\ldots,-2),\quad\varepsilon=n^{-20}.$$
--   For item 0 let $R_0$ admit every predecessor set except $\{2\}$ and $\{1,2,3\}$. Then $\theta^+$ is an alternative with legal-swap signal $\Delta(\theta^+,R_0)=1$, which eventually exceeds $C\sqrt{\log n/(npL)}$ for every $C>0$; $\theta^-$ is a null; all model, density and scaling conditions hold; and $P_{\theta^+}(A_t)-P_{\theta^-}(A_t)\to0$ for every sequence of events. Hence, at $\alpha=1/4$, $\limsup P_{\theta^-}(\text{reject})\le 1/4$ and $P_{\theta^+}(\text{reject})\to1$ cannot both hold. Together with the first part, the printed power claim fails on the full property domain of Definition 2.3.
--
--   This is the corrected form of Theorem 3.4: its Type I clause at full strength, and an explicit refutation of its power clause.
--
--   Differences from the source:
--   - correction: the power clause inf_{γ*∈Ri, Δ(θ*,Ri)>δ} P(Reject H0) → 1 with δ = C√(log n/(npL)), for every Definition 2.3 property → an explicit bounded-range, rate-compliant null/alternative witness with legal-swap signal 1 for which Type I control at α = 1/4 and power tending to one cannot hold together; with the first conjunct this refutes the power clause; reason: DISPROOF.md C3: the two data laws have total variation tending to zero; the first inclusion on p. 56 treats the legal-swap distance as the distance to the whole null region, which fails for general unions of equivalence classes
--   - reading: sup_{γ*∉Ri} P0(Reject H0) ≤ α as n,L → ∞ → for every sequence of null parameters (γ(θ*) ∉ Ri), items and properties, the eventual bound P(reject) ≤ α + ε for each ε > 0 (limsup ≤ α); reason: the proof on p. 55 ends with ≤ α + o(1); quantifying over all null sequences is equivalent to a limsup of the supremum over nulls
--   - encoding: sample size n and repeated-comparison count L tend to infinity → a separate sequence index t, dimensions n(t), L(t), and finite product probability spaces; reason: the law at each problem size is exactly (2.1); both graph and comparison randomness remain
--   - encoding: rankings and legal pairs without a tie rule → increasing-index tie resolution; reason: the witness has no ties involving the tested item or the three distinguished opponents; ties among lower items do not change its predecessor set or legal pairs
-- source:
--   Liu, Fang, Lu, Lagrangian Inference for Ranking Problems, arXiv:2110.00151v1, p. 24, Theorem 3.4; proof pp. 54–56

import Mathlib
import Definitions.Def_LagrangeRank_Debias_Supplement_Witnesses

namespace LagrangeRank.Debias.Supplement

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ENNReal
/-- Theorem 3.4 corrected: uniform asymptotic Type I control of the general full-box test holds;
the power clause is refuted by an explicit bounded-range, rate-compliant witness. -/
theorem theorem_3_4 (κ c α : ℝ) (hκ : 1 ≤ κ) (hc : 0 < c) (hα : 0 < α ∧ α < 1) :
    (∃ C0 : ℝ, 0 < C0 ∧
      ∀ (n L : ℕ → ℕ) (p : ℕ → unitInterval) (θ : (t : ℕ) → Vec (n t))
        (i : (t : ℕ) → Fin (n t)) (R : (t : ℕ) → Set (Ranking (n t))),
        Regime n L p → Density C0 n p → Rates32 n L p → Rates33 n L p →
        (∀ t, Parameter κ (θ t)) → (∀ t, RankingProperty (i t) (R t)) →
        (∀ t, ranking (θ t) ∉ R t) →
        AsymptoticUpper (fun t => (dataLaw (L t) (p t) (θ t)
          {s | singleReject (p t) c α (i t) (R t) s}).toReal) α) ∧
    (Regime witnessN witnessL (fun _ => 1) ∧
    Rates32 witnessN witnessL (fun _ => 1) ∧ Rates33 witnessN witnessL (fun _ => 1) ∧
    (∀ C0 : ℝ, Density C0 witnessN (fun _ => 1)) ∧
    (∀ t, Parameter (Real.exp 4) (nearScores t true) ∧
      Parameter (Real.exp 4) (nearScores t false) ∧
      RankingProperty (item0 t) (witnessProperty t) ∧
      ranking (nearScores t true) ∈ witnessProperty t ∧
      ranking (nearScores t false) ∉ witnessProperty t ∧
      signal (nearScores t true) (item0 t) (witnessProperty t) = 1) ∧
    (∀ C : ℝ, 0 < C → ∀ᶠ t in atTop,
      ENNReal.ofReal (C * signalScale (witnessN t) (witnessL t) 1) <
        signal (nearScores t true) (item0 t) (witnessProperty t)) ∧
    (∀ A : (t : ℕ) → Set (Data (witnessN t) (witnessL t)),
      Tendsto (fun t => nearProb t true (A t) - nearProb t false (A t)) atTop (𝓝 0)) ∧
    ¬(AsymptoticUpper (fun t => nearProb t false
        {s | singleReject 1 1 (1/4) (item0 t) (witnessProperty t) s}) (1/4) ∧
      Tendsto (fun t => nearProb t true
        {s | singleReject 1 1 (1/4) (item0 t) (witnessProperty t) s}) atTop (𝓝 1))) := by sorry

end LagrangeRank.Debias.Supplement
