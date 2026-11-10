-- Prove2me | Theorems.Thm_GibbsTransition_SizeCopies_adaptive_cost_lower_bound
-- name    : GibbsTransition.SizeCopies.adaptive_cost_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T21:54:51.172739+00:00
-- url     : https://prove2.me/theorems/5414b9f6-0799-463b-bfb0-fb6030447c9d
-- title:
--   Lemma 5.3 — Cost bound from approximate equality
-- statement:
--   Let rational $0<\varepsilon\le1/16$, $\varepsilon/2<\varepsilon'\le\varepsilon$, $\beta>0$ and $0<\delta<1/2$ be given. Put $R=\lfloor\kappa/\varepsilon\rfloor$ and take the actual ferromagnets $r_0=0$, $r_1=4\varepsilon'$. Every measurable adaptive experiment that terminates almost surely and estimates the transition within $\varepsilon$ with error probability at most $\delta$ under both instances satisfies, separately under each instance,
--
--   $$\mathbb E_i[V]\ge\frac{1-2\delta}{\xi_{\beta,R}+(R+1)^{-3}}.$$
--
--   Here $V$ counts all supplied spins and $\xi$ is the entire expression in (30). There is no size cap. Retained quantum memory, collective instruments, arbitrary measurable outcomes and unbounded stopping times are allowed. Infinite expected costs satisfy the displayed inequality.
--
--   Differences from the source:
--   - encoding: fresh-state instruments, almost-sure stopping and expected costs → arbitrary-basis trace-class matrix kernels, CP event maps, induced finite-horizon laws and ENNReal limits; reason: complete positivity, Born consistency and trace preservation describe the same instruments; absorbing finite horizons recover stopped output laws and nonnegative costs, including infinity
--   - generalization: classically controlled algorithms → all measurable instance-independent classical policies and instruments, without an effectiveness requirement on the lower-bound adversary; reason: every source algorithm is such a policy; the same fresh-state hybrid estimate applies, and the full source claim is obtained by restriction
-- source:
--   Yuhao Cai, Zhenzhang Li, STOC 2027 submission #1168 (October 2026), Lemma 5.3, Equation (33), printed p. 11 (PDF p. 13), with §5.2 preamble, printed p. 10 (PDF p. 12); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1168.pdf

import Mathlib
import Definitions.Def_GibbsTransition_SizeCopies_Experiment

set_option autoImplicit false

open scoped ENNReal

namespace GibbsTransition.SizeCopies

/-- Lemma 5.3 with the entire Section 5.2 preamble. There is no size cap,
memory bound, finite outcome set, or deterministic stopping horizon. -/
theorem adaptive_cost_lower_bound (epsilon epsilon' beta delta : ℚ)
    (he0 : 0 < epsilon) (he1 : epsilon ≤ 1/16)
    (hep0 : epsilon/2 < epsilon') (hep1 : epsilon' ≤ epsilon)
    (hb : 0 < beta) (hd0 : 0 < delta) (hd1 : delta < 1/2)
    (O ι : Type) [MeasurableSpace O] (A : Experiment O ι)
    (hA : IsExperiment A)
    (hcorrect : ∀ i : Fin 2,
      experimentCorrect A (ferromagnet (if i = 0 then 0 else 4*(epsilon' : ℝ)))
        beta epsilon delta) :
    let R := ⌊kappa / (epsilon : ℝ)⌋₊
    ∀ i : Fin 2,
      ENNReal.ofReal ((1 - 2*(delta : ℝ)) /
        (xi beta R + (((R : ℝ)+1)^3)⁻¹)) ≤
      experimentSpins A (ferromagnet (if i = 0 then 0 else 4*(epsilon' : ℝ))) beta := by sorry

end GibbsTransition.SizeCopies
