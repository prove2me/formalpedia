-- Prove2me | Theorems.Thm_MeanCertificates1424_Hardness_Supplement_theorem_3_11
-- name    : MeanCertificates1424.Hardness.Supplement.theorem_3_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T08:59:16.900513+00:00
-- url     : https://prove2.me/theorems/2ba863a3-4413-417c-ae64-3e822f7fcab1
-- title:
--   Theorem 3.11 — NP-hardness with two report values and small fractions
-- statement:
--   Upper-Mean is NP-hard on connected split graphs with reports in $\{0,3\}$, $L=1$, $\epsilon=0$, no audits, uniform weights and $b<n$; this remains true with $b\le\rho n$ for an arbitrary fixed rational $\rho\in(0,1)$. The constructed instances are feasible: the reductions output only feasible instances of the class.
--
--   With only two report values, exact certification is hard for every fixed corruption fraction.
--
--   Differences from the source:
--   - reading: Upper-Mean is hard on a restricted class → every NP language (resp. p-Clique) reduces to the restricted language by a reduction whose outputs always lie in the class; reason: hardness of a problem restricted to a class means reductions into that class
--   - encoding: even with b ≤ ρn for an arbitrary fixed rational ρ ∈ (0,1) → the statement for ρ = 1 (no restriction) and for every rational ρ ∈ (0,1); reason: b ≤ 1·n is the standing assumption
-- source:
--   chaomeng chen, Junhao Dong, STOC 2027 submission #1424 (October 2026), Theorem 3.11, printed p.11 (PDF p.13), proof to printed p.12 (PDF p.14)

import Mathlib
import Definitions.Def_MeanCertificates1424_Hardness_Supplement_Complexity

set_option autoImplicit false

open MeanCertificates1424.Hardness

namespace MeanCertificates1424.Hardness.Supplement

/-- Theorem 3.11, printed p.11 / PDF p.13 (proof to p.12 / PDF p.14). Upper-Mean is NP-hard on
connected split graphs with reports in `{0, 3}`, `L = 1`, `ε = 0`, no audits and uniform
weights, also with `b ≤ ρ n` for every fixed rational `ρ ∈ (0,1)`; the reductions output
feasible instances of the class. -/
theorem theorem_3_11 :
    NPHardOn (UMLang (TwoValSplit 1))
      (fun w => ∃ (I : UniformInstance) (θ : ℚ), w = encUM I θ ∧ TwoValSplit 1 I ∧
        (feasible I).Nonempty) ∧
    ∀ ρ : ℚ, 0 < ρ → ρ < 1 →
      NPHardOn (UMLang (TwoValSplit ρ))
        (fun w => ∃ (I : UniformInstance) (θ : ℚ), w = encUM I θ ∧ TwoValSplit ρ I ∧
          (feasible I).Nonempty) := by sorry

end MeanCertificates1424.Hardness.Supplement
