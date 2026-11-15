-- Prove2me | Theorems.Thm_GibbsTransition_SizeCopies_Supplement_approximate_energy_comparisons
-- name    : GibbsTransition.SizeCopies.Supplement.approximate_energy_comparisons
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T05:41:07.542606+00:00
-- url     : https://prove2.me/theorems/4b67a4c9-5953-4b2a-b20e-009dad897caf
-- title:
--   Lemma 6.2 — Comparisons from approximate energies
-- statement:
--   Let $u$ be any instance of the general field-coupled class, with public gap $d=b-a$ and $C_*=\max(1,12J)$. Let the rational Hermitian reconstructed local terms satisfy the preceding uniform energy bound
--   $$|\widehat e_L(\phi)-(e_u(\phi)-c_u)|\le\Delta+C_*/L,\qquad0\le\Delta\le d\epsilon/128,$$
--   for every positive size and real $\phi\in[0,1]$, where $c_u$ is the field-independent canonical scalar shift and rational $0<\epsilon\le1/16$. Then the specified deterministic rational finite-energy search returns a rational estimate with
--   $$|\widehat\theta-\theta_u|\le\epsilon.$$
--   Its classically constructed cubes have side at most $C_s C_*/(d\epsilon)$ for a universal positive constant $C_s$; $65$ is admissible from $L\le64C_*/(d\epsilon)+1$.
--
--   The search uses exact rational Schur tests and bisection, including singular-pivot equality cases. These computed cubes do not consume supplied spins or copies.
--
--   Differences from the source:
--   - encoding: rational estimates obey the preceding bound and the following search → explicit scalar shift, uniform bound (52), and finite rational Schur/bisection implementation; reason: the field-independent shift cancels from secants; the implementation supplies the stated finite energies
--   - generalization: a boundary prescription with a uniform effective algebraic encoding → an algebraic Hermitian boundary prescription with a uniform computable rational Cauchy table; reason: an effective algebraic encoding supplies this table; the statements use only certified approximations and the same surface norm bound, so every source boundary is included without requiring uniform recovery of exact algebraic descriptions
-- source:
--   Yuhao Cai, Zhenzhang Li, STOC 2027 submission #1168 (October 2026), Lemma 6.2, printed p. 15 (PDF p. 17); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1168.pdf

import Mathlib
import Definitions.Def_GibbsTransition_SizeCopies_Supplement_Numerics
open MeasureTheory
open scoped ENNReal Matrix.Norms.L2Operator
set_option autoImplicit false

namespace GibbsTransition.SizeCopies.Supplement

theorem approximate_energy_comparisons :
    ∃ Cs : ℝ, 0 < Cs ∧ ∀ (q : ℕ) (hq : 0 < q) (p : FieldData q),
    ValidField p → ∀ (u : FieldInteraction q), InFieldClass p u →
    ∀ (epsilon : ℚ), 0 < epsilon → epsilon ≤ 1/16 →
    ∀ (r : RationalTerms q) (Delta : ℝ),
      EnergyApproximation p u r Delta → Delta ≤ (gap p : ℝ)*epsilon/128 →
      |(energySearch hq p r epsilon : ℝ)-fieldTheta p u| ≤ epsilon ∧
      ∀ k < groundRounds epsilon,
        (energySide p k : ℝ) ≤ Cs*(recoveryC p : ℝ)/((gap p : ℝ)*(epsilon : ℝ)) := by sorry

end GibbsTransition.SizeCopies.Supplement
