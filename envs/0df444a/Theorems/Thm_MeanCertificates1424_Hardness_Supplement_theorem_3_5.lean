-- Prove2me | Theorems.Thm_MeanCertificates1424_Hardness_Supplement_theorem_3_5
-- name    : MeanCertificates1424.Hardness.Supplement.theorem_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T08:57:02.951732+00:00
-- url     : https://prove2.me/theorems/83a2505e-833f-4136-83f8-3c583f7d01df
-- title:
--   Theorem 3.5 — Upper-Mean is W[1]-hard in b and NP-complete on zero-report split graphs
-- statement:
--   **Upper-Mean** asks, for an anchored rational instance and a threshold $\theta$, whether the feasible class is nonempty with upper endpoint $u(y)\ge\theta$. Consider the class of instances on connected split graphs of diameter at most two with $L=1$, $\epsilon=0$, no audits, uniform weights, report $y=0$ and $b<n$.
--
--   1. Upper-Mean on this class, parameterized by $b$, is W[1]-hard.
--   2. Upper-Mean on this class is NP-complete.
--   3. For every fixed rational $\rho\in(0,1)$, both statements hold on the subclass with $b\le\rho n$.
--   4. Every instance of the class is feasible and symmetric ($x$ feasible implies $-x$ feasible), has minimax point estimate $(\ell+u)/2=0$, and has upper endpoint in $n^{-1}\mathbb Z$.
--
--   The hardness reductions output instances of the respective class. This is the budget-parameter hardness of exact certification, even when all reports agree.
--
--   **Formalization Note** Instances are the mission's published rational uniform unaudited instances with their binary encoding, followed by the binary threshold.
--
--   Differences from the source:
--   - encoding: W[1]-hard → fpt many-one reducible from p-Clique with the new parameter bounded by a computable function of k; reason: standard W[1]-completeness of p-Clique; the brief prescribes this equivalence
--   - reading: Upper-Mean is hard on a restricted class → every NP language (resp. p-Clique) reduces to the restricted language by a reduction whose outputs always lie in the class; reason: hardness of a problem restricted to a class means reductions into that class
--   - generalization: the constructed instances are feasible and symmetric, have minimax point estimate 0 and upper endpoint in n⁻¹ℤ → every instance of the class has these properties; reason: with y=0 the zero field is feasible, negation preserves the constraints and Lemma 3.4 gives u=Ψ_G(b)/n; this specializes to the constructed instances
--   - encoding: for every fixed rational ρ ∈ (0,1) all statements hold with b ≤ ρn → the same conjunction for the class with the extra constraint b ≤ ρn, ρ = 1 standing for no restriction; reason: b ≤ 1·n is the standing assumption
-- source:
--   chaomeng chen, Junhao Dong, STOC 2027 submission #1424 (October 2026), Theorem 3.5, printed p.9 (PDF p.11), proof to printed p.10 (PDF p.12)

import Mathlib
import Definitions.Def_MeanCertificates1424_Hardness_Supplement_Complexity

set_option autoImplicit false

open MeanCertificates1424.Hardness

namespace MeanCertificates1424.Hardness.Supplement

/-- Theorem 3.5, printed p.9 / PDF p.11 (proof to p.10 / PDF p.12). Upper-Mean on connected
split graphs of diameter at most two with `L = 1`, `ε = 0`, no audits, uniform weights and
`y = 0`: W[1]-hard in `b` and NP-complete; the same for every fixed rational `ρ ∈ (0,1)`
with `b ≤ ρ n`; every such instance is feasible and symmetric, has minimax point estimate
`0`, and has upper endpoint in `n⁻¹ ℤ`. Hardness reductions output instances of the class. -/
theorem theorem_3_5 :
    (W1HardOn (UMLang (ZeroSplit 1)) umBudget (UMOut (ZeroSplit 1)) ∧
      InNP (UMLang (ZeroSplit 1)) ∧ NPHardOn (UMLang (ZeroSplit 1)) (UMOut (ZeroSplit 1))) ∧
    (∀ ρ : ℚ, 0 < ρ → ρ < 1 →
      W1HardOn (UMLang (ZeroSplit ρ)) umBudget (UMOut (ZeroSplit ρ)) ∧
      InNP (UMLang (ZeroSplit ρ)) ∧ NPHardOn (UMLang (ZeroSplit ρ)) (UMOut (ZeroSplit ρ))) ∧
    (∀ I : UniformInstance, ZeroSplit 1 I →
      (feasible I).Nonempty ∧ (∀ x ∈ feasible I, -x ∈ feasible I) ∧
      Hardness.lower I = -Hardness.upper I ∧
      ((Hardness.lower I).toReal + (Hardness.upper I).toReal) / 2 = 0 ∧
      ∃ z : ℤ, Hardness.upper I = (((z : ℝ) / I.n : ℝ) : EReal)) := by sorry

end MeanCertificates1424.Hardness.Supplement
