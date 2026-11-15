-- Prove2me | Theorems.Thm_GibbsTransition_SizeCopies_Supplement_ground_size_lower_bound
-- name    : GibbsTransition.SizeCopies.Supplement.ground_size_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T05:39:53.160207+00:00
-- url     : https://prove2.me/theorems/b2980ac5-f4c7-4739-83aa-aa56df92b8ab
-- title:
--   Theorem 4.4 — Ground-state size lower bound
-- statement:
--   For each rational $0<\epsilon\le1/16$, there are two instances of the published class, chosen before the confidence and learner, with the following property. Every ground-state learner terminating almost surely and having error at most rational $0<\delta<1/2$ on both satisfies, under each instance, with $R=\lfloor\kappa/\epsilon\rfloor$,
--   $$\Pr\{L_{\max}>R\}\ge1-2\delta,\qquad\mathbb E[V]\ge(1-2\delta)(R+1)^3.$$
--   There is no size cap on the learner. Instruments, retained memory, fields and stopping can be adaptive; ground copies are normalized projectors onto the full ground spaces.
--
--   The probability and expected-spin inequalities give distinct parts of the size obstruction, and the same hard pair supplies both under both instances.
--
--   Differences from the source:
--   - encoding: ground copies, random maximum side and expected spins → explicit ground supplier, ever-oversized query event, and extended nonnegative stopped expectation; reason: the event is exactly L_max>R on almost-surely terminating runs, with no finite-expectation requirement
-- source:
--   Yuhao Cai, Zhenzhang Li, STOC 2027 submission #1168 (October 2026), Theorem 4.4, printed p. 8 (PDF p. 10); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1168.pdf

import Mathlib
import Definitions.Def_GibbsTransition_SizeCopies_Supplement_Access
open MeasureTheory
open scoped ENNReal Matrix.Norms.L2Operator
set_option autoImplicit false

namespace GibbsTransition.SizeCopies.Supplement

theorem ground_size_lower_bound (epsilon : ℚ)
    (he : 0 < epsilon) (hemax : epsilon ≤ 1/16) :
    ∃ u0 u1 : Interaction, InClass u0 ∧ InClass u1 ∧
    ∀ delta : ℚ, 0 < delta → delta < 1/2 →
    ∀ (O ι : Type) [MeasurableSpace O] (A : AccessExperiment 3 O ι),
    IsAccessExperiment A →
    accessCorrect A (starSupplier u0 .ground) (transitionPoint u0) epsilon delta →
    accessCorrect A (starSupplier u1 .ground) (transitionPoint u1) epsilon delta →
    ∀ u ∈ ({u0,u1} : Set Interaction),
      ENNReal.ofReal (1-2*(delta : ℝ)) ≤
        oversizedProbability A (starSupplier u .ground) ⌊kappa/(epsilon : ℝ)⌋₊ ∧
      ENNReal.ofReal ((1-2*(delta : ℝ)) *
        ((⌊kappa/(epsilon : ℝ)⌋₊ : ℝ)+1)^3) ≤ accessSpins A (starSupplier u .ground) := by sorry

end GibbsTransition.SizeCopies.Supplement
