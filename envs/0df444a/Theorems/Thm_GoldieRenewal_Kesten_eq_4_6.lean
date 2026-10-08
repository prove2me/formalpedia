-- Prove2me | Theorems.Thm_GoldieRenewal_Kesten_eq_4_6
-- name    : GoldieRenewal.Kesten.eq_4_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:11:48.56623+00:00
-- url     : https://prove2.me/theorems/28032047-c9d0-4fe1-bfff-ad9ac0ff1a15
-- title:
--   (4.6) — P(sup_j |R_j + Π_j med R| > x) ≤ 2P(|R| > x) for x ≥ 0
-- statement:
--   Let $(Q,M)$ have joint law $\mu$, let $M$ satisfy the conditions of Lemma 2.2 for some $\kappa>0$, and let $\mathbf E|Q|^\kappa<\infty$. Let $(Q_n,M_n)$, $n\ge1$, be independent copies of $(Q,M)$ with partial products $\Pi_j=M_1\cdots M_j$ and partial sums $R_j=\sum_{k=1}^j\Pi_{k-1}Q_k$. Let $R$ have the law $\rho$ solving $R\overset{\mathcal L}{=}Q+MR$, and let $\mathrm{med}\,R$ be any median of $\rho$. Then
--
--   $$
--   P\Big(\sup_{j\ge 1}\big|R_j+\Pi_j\,\mathrm{med}\,R\big|>x\Big)\le 2P\big(|R|>x\big),\qquad x\ge 0 .
--   $$
--
--   It is obtained from Proposition 4.2 by letting $n\to\infty$ (with $y=0$) and combining with the same inequality for $-R$. In the proof of Theorem 4.1 it gives the lower bound on $P(|R|>t)$ that makes $C_++C_->0$ under (4.5).
--
--   **Formalization Note** The supremum ranges over $j\ge1$, the range of Proposition 4.2; "the supremum exceeds $x$" is written as "some $j$ has the term exceeding $x$". The statement is made for every law solving the equation (by Theorem 4.1 there is exactly one) and every median of it.
-- source:
--   Goldie, Implicit renewal theory and tails of solutions of random equations, Ann. Appl. Probab. 1(1):126–166 (1991), DOI 10.1214/aoap/1177005985, p. 136, (4.6)

import Mathlib
import Definitions.Def_GoldieRenewal_Implicit_CramerConditions
import Definitions.Def_GoldieRenewal_Kesten_RandomDifferenceEquation
import Definitions.Def_GoldieRenewal_Kesten_Perpetuity

namespace GoldieRenewal.Kesten

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- **(4.6)** (Goldie, *Implicit renewal theory and tails of solutions of random equations*,
Ann. Appl. Probab. 1(1) (1991), p. 136, derived from Proposition 4.2 in the text). Under the
conditions of Theorem 4.1, let `(Q_n, M_n)`, `n = 1, 2, …`, be independent with the law `μ` of
`(Q, M)`, with `Π_j`, `R_j` as in Proposition 4.2. Let `R` have the law `ρ` solving (1.1) and let
`med R` be a median of `ρ`. Then
`P(sup_{j ∈ ℕ} |R_j + Π_j med R| > x) ≤ 2 P(|R| > x)` for all `x ≥ 0`.

**Formalization Note** The sequence is stored 0-based (`Q i`, `M i` are the paper's `Q_{i+1}`,
`M_{i+1}`). `j` ranges over `j ≥ 1`, the range of Proposition 4.2 from which (4.6) is derived.
"sup > x" is "some `j` has `… > x`". `P(|R| > x)` is `ρ{r : |r| > x}`. Stated for every law
solving (1.1) (unique by Theorem 4.1) and every median of it. -/
theorem eq_4_6 (κ : ℝ) (μ : Measure (ℝ × ℝ)) [IsProbabilityMeasure μ]
    (hM : GoldieRenewal.Implicit.CramerConditions κ (μ.map Prod.snd))
    (hQ : ∫⁻ p, ENNReal.ofReal (|p.1| ^ κ) ∂μ < ∞)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Q M : ℕ → Ω → ℝ) (hQm : ∀ i, Measurable (Q i)) (hMm : ∀ i, Measurable (M i))
    (hindep : iIndepFun (fun i ω => (Q i ω, M i ω)) P)
    (hlaw : ∀ i, P.map (fun ω => (Q i ω, M i ω)) = μ)
    (ρ : ProbabilityMeasure ℝ) (hρ : rdeOperator μ (ρ : Measure ℝ) = ρ)
    (a : ℝ) (ha : IsMedian (ρ : Measure ℝ) a) (x : ℝ) (hx : 0 ≤ x) :
    P {ω | ∃ j : ℕ, 1 ≤ j ∧ x < |partialSum Q M j ω + piProd M j ω * a|}
      ≤ 2 * (ρ : Measure ℝ) {r | x < |r|} := by sorry

end GoldieRenewal.Kesten
