-- Prove2me | Theorems.Thm_GibbsTransition_SizeCopies_Supplement_temperature_regimes
-- name    : GibbsTransition.SizeCopies.Supplement.temperature_regimes
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T05:45:54.883372+00:00
-- url     : https://prove2.me/theorems/9f8aa7c9-1b5a-48ec-8119-fe0f98fc1e00
-- title:
--   Theorem 3.2 — Temperature regimes
-- statement:
--   At confidence $9/10$, the published class exhibits three estimation regimes. All statements apply for rational $0<\epsilon\le1/16$.
--
--   1. For each fixed rational $\beta>0$, one-site and eight-site Gibbs states at field zero admit a learner with at most $C_\beta\epsilon^{-2}$ copies. Every correct learner capped at side two, with arbitrary adaptive collective measurements, has worst-case expected copy count at least $[\log10/(64\beta^2)]\epsilon^{-2}$.
--   2. For ground-state access, one pair of instances forces every uniformly correct learner to satisfy $\Pr_u\{L_{\max}>\lfloor\kappa/\epsilon\rfloor\}\ge4/5$ under each member. The specified ground learner has side $O(\epsilon^{-1})$ and $O(\log^2(1/\epsilon))$ copies.
--   3. Absolute positive constants, fixed before both inputs, give
--   $$c\epsilon^{-3}\le V_\beta^*(\epsilon)\le C\epsilon^{-3}\qquad(\beta\ge512/\epsilon).$$
--   The explicit upper learner uses side $O(\epsilon^{-1})$, $O(\log^2(1/\epsilon))$ copies and $O(\epsilon^{-3})$ supplied spins. Lower learners have unrestricted memory, outcomes and almost-sure stopping.
--
--   This aggregate statement keeps all three regimes and both directions of their complexity comparisons.
--
--   Differences from the source:
--   - encoding: big-O/Omega regime bounds and state-copy learners → uniform positive constants, specified finite Born output laws, and ENNReal stopped costs; reason: the schedules and lower constants come from the source proofs; all original regimes and learner access are retained
-- source:
--   Yuhao Cai, Zhenzhang Li, STOC 2027 submission #1168 (October 2026), Theorem 3.2, printed p. 5 (PDF p. 7); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1168.pdf

import Mathlib
import Definitions.Def_GibbsTransition_SizeCopies_Supplement_Tomography
import Definitions.Def_GibbsTransition_SizeCopies_Supplement_LowTemperature
open MeasureTheory
open scoped ENNReal Matrix.Norms.L2Operator
set_option autoImplicit false

namespace GibbsTransition.SizeCopies.Supplement

theorem temperature_regimes :
    ∃ Cgs Cgn clo chi Cls Cln : ℝ,
      0 < Cgs ∧ 0 < Cgn ∧ 0 < clo ∧ 0 < chi ∧ 0 < Cls ∧ 0 < Cln ∧
    (∀ beta : ℚ, 0 < beta → ∃ (Cf : ℝ) (mu : ℚ) (v : PublicNumerics),
      0 < Cf ∧ 0 < mu ∧ EffectivePublic starData v ∧
      ∀ epsilon : ℚ, 0 < epsilon → epsilon ≤ 1/16 →
        (tomographyCopies starData beta mu epsilon (1/10) : ℝ) ≤ Cf*(epsilon : ℝ)⁻¹^2 ∧
        (∀ u : Interaction, InClass u →
          LawCorrect (tomographyFinal (by norm_num : 0 < 3) starData v (starInteraction u)
            beta mu epsilon (1/10)) (transitionPoint u) epsilon (1/10)) ∧
        ∀ (O ι : Type) [MeasurableSpace O] (A : Experiment O ι),
          IsExperiment A → LearnsClass A beta epsilon (1/10) →
          (∀ u, InClass u → experimentCap A u beta 2) →
          ENNReal.ofReal ((Real.log 10/(64*(beta : ℝ)^2))*(epsilon : ℝ)⁻¹^2) ≤
            ⨆ u : {u : Interaction // InClass u}, experimentCopies A u.val beta) ∧
    (∀ epsilon : ℚ, 0 < epsilon → epsilon ≤ 1/16 →
      (∃ u0 u1 : Interaction, InClass u0 ∧ InClass u1 ∧
        ∀ (O ι : Type) [MeasurableSpace O] (A : AccessExperiment 3 O ι),
          IsAccessExperiment A →
          (∀ u, InClass u → accessCorrect A (starSupplier u .ground) (transitionPoint u) epsilon (1/10)) →
          ∀ u ∈ ({u0,u1} : Set Interaction),
            (4/5 : ℝ≥0∞) ≤ oversizedProbability A (starSupplier u .ground) ⌊kappa/(epsilon : ℝ)⌋₊) ∧
      (groundCopies starData epsilon (1/10) : ℝ) ≤ Cgn*(Real.log (1/(epsilon : ℝ)))^2 ∧
      (∀ k < groundRounds epsilon, (groundSide starData k : ℝ) ≤ Cgs/(epsilon : ℝ)) ∧
      ∀ u : Interaction, InClass u →
        LawCorrect (groundFinal starData (starInteraction u) epsilon (1/10))
          (transitionPoint u) epsilon (1/10)) ∧
    (∀ epsilon beta : ℚ, 0 < epsilon → epsilon ≤ 1/16 → 512/epsilon ≤ beta →
      ENNReal.ofReal (clo*(epsilon : ℝ)⁻¹^3) ≤ spinMinimax beta epsilon ∧
      spinMinimax beta epsilon ≤ ENNReal.ofReal (chi*(epsilon : ℝ)⁻¹^3) ∧
      (groundCopies starData epsilon (1/10) : ℝ) ≤ Cln*(Real.log (1/(epsilon : ℝ)))^2 ∧
      (largeGibbsSpins epsilon (1/10) : ℝ) ≤ chi*(epsilon : ℝ)⁻¹^3 ∧
      (∀ k < groundRounds epsilon, (largeGibbsSide k : ℝ) ≤ Cls/(epsilon : ℝ)) ∧
      ∀ u : Interaction, InClass u →
        LawCorrect (largeGibbsFinal u beta epsilon (1/10)) (transitionPoint u) epsilon (1/10)) := by sorry

end GibbsTransition.SizeCopies.Supplement
