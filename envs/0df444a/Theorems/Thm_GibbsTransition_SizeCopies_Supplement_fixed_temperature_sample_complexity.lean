-- Prove2me | Theorems.Thm_GibbsTransition_SizeCopies_Supplement_fixed_temperature_sample_complexity
-- name    : GibbsTransition.SizeCopies.Supplement.fixed_temperature_sample_complexity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T05:42:19.287853+00:00
-- url     : https://prove2.me/theorems/3b5e0ce6-1e7e-4a23-9ea0-c1bdf53c870e
-- title:
--   Theorem 6.3 — Fixed-temperature sample complexity
-- statement:
--   Fix local dimension $q=3$, public rational bounds $J>0,J_b\ge0$, gap $0<d\le1$, and inverse temperature $\beta>0$. A finite constant $C_{\beta,q,J,J_b,d}$ is fixed before accuracy, confidence, the unknown interaction, and the choice of public effect and boundary with those bounds. For every such general field-coupled class and rational $0<\epsilon\le1/16$, $0<\delta\le1/4$, the specified separate-copy tomography and finite-energy learner is correct and uses only Gibbs states at sides one and two and field zero, with
--   $$N\le C_{\beta,q,J,J_b,d}\epsilon^{-2}\log(1/\delta),\qquad V\le8N.$$
--   The public recursive approximation table and a rational spectral-floor parameter are fixed before accuracy, confidence and the unknown interaction. The unknown terms and transition never enter this public data. Every outcome produces a rational, terminating finite-energy computation.
--
--   The constant follows from (45), (50) and (56); the good-event energy error is bounded by $\Delta\le d\epsilon/128$. The theorem adds no classical polynomial-time requirement.
--
--   Differences from the source:
--   - encoding: effectively encoded public algebraic data and an algorithm with O sample count → recursive Cauchy table, rational positive mu, exact finite tomography/output law and a uniform positive constant; reason: algebraic public entries and the prescribed effective boundary admit this table; it contains no unknown data
--   - generalization: a boundary prescription with a uniform effective algebraic encoding → an algebraic Hermitian boundary prescription with a uniform computable rational Cauchy table; reason: an effective algebraic encoding supplies this table; the statements use only certified approximations and the same surface norm bound, so every source boundary is included without requiring uniform recovery of exact algebraic descriptions
-- source:
--   Yuhao Cai, Zhenzhang Li, STOC 2027 submission #1168 (October 2026), Theorem 6.3, printed p. 15 (PDF p. 17); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1168.pdf

import Mathlib
import Definitions.Def_GibbsTransition_SizeCopies_Supplement_Tomography
open MeasureTheory
open scoped ENNReal Matrix.Norms.L2Operator
set_option autoImplicit false

namespace GibbsTransition.SizeCopies.Supplement

theorem fixed_temperature_sample_complexity
    (J Jb d beta : ℚ) (hJ : 0 < J) (hJb : 0 ≤ Jb)
    (hd : 0 < d) (hdmax : d ≤ 1) (hb : 0 < beta) :
    ∃ (C : ℝ) (mu : ℚ), 0 < C ∧ 0 < mu ∧
    ((3 : ℝ)^(-8 : ℤ)*Real.exp (-2*(beta : ℝ)*(20*J+4*Jb)))/4 ≤ (mu : ℝ) ∧
    (mu : ℝ) ≤ ((3 : ℝ)^(-8 : ℤ)*Real.exp (-2*(beta : ℝ)*(20*J+4*Jb)))/2 ∧
    ∀ p : FieldData 3, ValidField p → p.J = J → p.Jb = Jb → gap p = d →
    ∃ v : PublicNumerics, EffectivePublic p v ∧
    ∀ epsilon delta : ℚ, 0 < epsilon → epsilon ≤ 1/16 → 0 < delta → delta ≤ 1/4 →
      (tomographyCopies p beta mu epsilon delta : ℝ) ≤
        C*(epsilon : ℝ)⁻¹^2*Real.log (1/(delta : ℝ)) ∧
      tomographySpins p beta mu epsilon delta ≤ 8*tomographyCopies p beta mu epsilon delta ∧
      ∀ u : FieldInteraction 3, InFieldClass p u →
        LawCorrect (tomographyFinal (by norm_num : 0 < 3) p v u beta mu epsilon delta)
          (fieldTheta p u) epsilon delta := by sorry

end GibbsTransition.SizeCopies.Supplement
