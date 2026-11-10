-- Prove2me | Theorems.Thm_GibbsTransition_SizeCopies_capped_copy_lower_bound
-- name    : GibbsTransition.SizeCopies.capped_copy_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T21:56:02.097025+00:00
-- url     : https://prove2.me/theorems/34bb35f6-c548-4462-ae2c-c076129597ad
-- title:
--   Corollary 5.5 — Copies below the size bound
-- statement:
--   Let rational $0<\varepsilon\le1/16$, $0<\delta\le1/4$ and $\beta\ge512/\varepsilon$. Every $(\varepsilon,\delta)$ learner on the entire noncommuting class $\mathcal C^*$, restricted almost surely under every instance to $L\le\lfloor\kappa/\varepsilon\rfloor$, satisfies on each of the two ferromagnets $r_0=0$, $r_1=4\varepsilon$,
--
--   $$\mathbb E_i[N]\ge(1-2\delta)\exp(13\kappa\beta/8).$$
--
--   The states are fresh Gibbs copies at the fixed temperature, the controls are dyadic, and general retained-memory collective instruments and almost-sure stopping are allowed. The hard pair is constructed rather than assumed. Rational accuracy permits the source choice $\varepsilon'=\varepsilon$.
--
--   Differences from the source:
--   - encoding: fresh-state instruments, almost-sure stopping and expected costs → arbitrary-basis trace-class matrix kernels, CP event maps, induced finite-horizon laws and ENNReal limits; reason: complete positivity, Born consistency and trace preservation describe the same instruments; absorbing finite horizons recover stopped output laws and nonnegative costs, including infinity
--   - generalization: classically controlled algorithms → all measurable instance-independent classical policies and instruments, without an effectiveness requirement on the lower-bound adversary; reason: every source algorithm is such a policy; the same fresh-state hybrid estimate applies, and the full source claim is obtained by restriction
--   - encoding: each of two instances from the proof → the explicit ferromagnets r=0 and r=4 epsilon; reason: accuracy is rational by §2.2, so the proof permits epsilon prime equal to epsilon, with disjoint success intervals
-- source:
--   Yuhao Cai, Zhenzhang Li, STOC 2027 submission #1168 (October 2026), Corollary 5.5, Equation (39), printed p. 12 (PDF p. 14); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1168.pdf

import Mathlib
import Definitions.Def_GibbsTransition_SizeCopies_Experiment

set_option autoImplicit false

open scoped ENNReal

namespace GibbsTransition.SizeCopies

/-- Corollary 5.5. The rational-accuracy hard pair is r=0 and r=4 epsilon.
The cost conclusion holds separately under each instance, including infinity. -/
theorem capped_copy_lower_bound (epsilon beta delta : ℚ)
    (he0 : 0 < epsilon) (he1 : epsilon ≤ 1/16)
    (hd0 : 0 < delta) (hd1 : delta ≤ 1/4) (hb : 512/epsilon ≤ beta)
    (O ι : Type) [MeasurableSpace O] (A : Experiment O ι)
    (hA : IsExperiment A) (hcorrect : LearnsClass A beta epsilon delta)
    (hcap : ∀ u, InClass u →
      experimentCap A u beta ⌊kappa / (epsilon : ℝ)⌋₊) :
    ∀ i : Fin 2,
      ENNReal.ofReal ((1 - 2*(delta : ℝ)) * Real.exp (13*kappa*(beta : ℝ)/8)) ≤
      experimentCopies A (ferromagnet (if i = 0 then 0 else 4*(epsilon : ℝ))) beta := by sorry

end GibbsTransition.SizeCopies
