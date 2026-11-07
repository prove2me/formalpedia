-- Prove2me | Theorems.Thm_KTCenter_lemma_6_2_potential
-- name    : KTCenter.lemma_6_2_potential
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:32:11.843665+00:00
-- url     : https://prove2.me/theorems/1166bc43-0fae-4a22-9375-63d52d9cd5a4
-- title:
--   Proof of Lemma 6.2 — the potential (79): $\Phi_0\le ne^{-4\ell}$, (81), (82), and every run satisfies (77); time carried by Theorem 6.1
-- statement:
--   Let $I$ be a cost instance with positive $C_0,C_1$, $0<\xi<1$, $\varphi\in\mathcal P(F)$, and a feasible solution of (LP1). Fix an order of the $m$ choices with all small-block indices first. Then:
--
--   1. $\Phi_0\le ne^{-4\ell}$;
--   2. at every prefix of positive probability, $\mathbb E[\Phi_j\mid\text{prefix}]\le\Phi_{j-1}$ (81);
--   3. for every evaluator that approximates $\Phi$ within $1/(8m)$ at every prefix of positive probability, a run of Algorithm 11 exists, and every run (with any tie-break) ends at an outcome $p$ with $\Phi_m\le\Phi_0+\frac14\le ne^{-4\ell}+\frac14<1$ (82) and
--   $$\tilde C_i(p)\le\mu_i+\gamma W\qquad(i\in[n]).\qquad(77)$$
--
--   The running-time clause of Lemma 6.2 is not part of this item; it is carried by Theorem 6.1. The case $m=0$ is included.
--
--   Differences from the source:
--
--   - generalization: Algorithm 11 with its evaluator and fixed tie order → every evaluator within 1/(8m) and every tie-break; reason: covers the algorithm's choice; it specializes to the source
--   - encoding: conditional expectations → quotients of finite sums over outcomes, used at prefixes of positive probability; reason: Lean convention; same values
-- source:
--   Chakraborty, Das, Mukherjee, Kendall–tau Center Admits a PTAS, STOC 2027 submission (manuscript sha256 4739ffba…), Lemma 6.2 and its proof, eqs. (77)–(82), pp.58–60 (PDF pp.60–62)

import Mathlib
import Definitions.Def_KTCenter_CostInstance
import Definitions.Def_KTCenter_FixKeys
import Definitions.Def_KTCenter_LP1
import Definitions.Def_KTCenter_Rounding

namespace KTCenter

/-- **Proof of Lemma 6.2**, eqs. (77), (79)–(82), pp.58–60 (PDF pp.60–62); time carried by
Theorem 6.1.

Chakraborty, Das, Mukherjee, *Kendall–tau Center Admits a PTAS*, STOC 2027 submission (manuscript
sha256 4739ffba…).

**Formalization Note.** Any `φ`, any feasible solution of (LP1), any fixed order of the choices with
the indices first. `Φ` is `CostInstance.Phi`. A run is stated for every evaluator within `1/(8m)` and
every tie-break, which covers Algorithm 11's choice. The prefix in (81) is that of the outcome `ω`, and
the conditional expectation is the quotient of finite sums. `m = 0` is included ("return φ"). -/
theorem lemma_6_2_potential {K : ℕ} {C₀ C₁ : ℚ} (hC₀ : 0 < C₀) (hC₁ : 0 < C₁)
    (I : CostInstance K C₀ C₁) (ξ : ℚ) (hξ0 : 0 < ξ) (hξ1 : ξ < 1)
    (φ : I.AssignOn (I.F ξ)) (g : I.LargeMember ξ) (fam : I.SmallFamily ξ)
    (P : I.LPPoint ξ fam) (hP : CostInstance.IsFeasible φ g P)
    (ord : Fin (CostInstance.numChoices I ξ) ≃ CostInstance.Choice I ξ)
    (hord : CostInstance.IndicesFirst ord) :
    (∀ ω, CostInstance.Phi φ P ord 0 ω ≤ (I.n : ℝ) * Real.exp (-(4 * (I.ell : ℝ)))) ∧
    (∀ (j : Fin (CostInstance.numChoices I ξ)) (ω : I.Outcome ξ fam),
      0 < CostInstance.prefixMass φ P ord j ω →
      (∑ ω' : I.Outcome ξ fam, open Classical in
          if CostInstance.SamePrefix ord j ω ω' then
            CostInstance.prob φ P ω' * CostInstance.Phi φ P ord ((j : ℕ) + 1) ω' else 0) /
        CostInstance.prefixMass φ P ord j ω ≤ CostInstance.Phi φ P ord j ω) ∧
    ∀ Ψ : ℕ → I.Outcome ξ fam → ℝ, CostInstance.IsEvaluator φ P ord Ψ →
      (∃ ω, CostInstance.IsRun φ P ord Ψ ω) ∧
      ∀ ω, CostInstance.IsRun φ P ord Ψ ω →
        CostInstance.Phi φ P ord (CostInstance.numChoices I ξ) ω ≤
          CostInstance.Phi φ P ord 0 ω + 1 / 4 ∧
        CostInstance.Phi φ P ord 0 ω + 1 / 4 ≤
          (I.n : ℝ) * Real.exp (-(4 * (I.ell : ℝ))) + 1 / 4 ∧
        (I.n : ℝ) * Real.exp (-(4 * (I.ell : ℝ))) + 1 / 4 < 1 ∧
        ∀ i : Fin I.n, (I.cost i (I.union ξ φ ω.2) : ℝ) ≤
          CostInstance.mu φ P i + ((CostInstance.gamma ξ * I.W : ℚ) : ℝ) := by sorry

end KTCenter
