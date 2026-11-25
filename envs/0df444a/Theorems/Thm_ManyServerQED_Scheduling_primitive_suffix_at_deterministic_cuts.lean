-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_primitive_suffix_at_deterministic_cuts
-- name    : ManyServerQED.Scheduling.primitive_suffix_at_deterministic_cuts
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-25T18:55:44.671242+00:00
-- url     : https://prove2.me/theorems/7cbeb0b9-248c-500c-9786-f4f34f826abd
-- title:
--   Joint law and prefix independence after deterministic primitive cuts
-- statement:
--   Fix a system and choose deterministic arrival indices $d_i$ and nonnegative service and abandonment cut times $p_i,q_i$. Let $Y$ collect the arrival count increments after the $d_i$-th arrival epochs, the service increments after $p_i$, and the abandonment increments after $q_i$, each indexed by all nonnegative elapsed times. Let $Y_0$ denote the same vector at the zero cuts, and $\mathcal H$ the sigma algebra of all primitive prefixes through the chosen cuts. Then $Y$ is independent of $\mathcal H$ and
--   $$\mathcal L(Y)=\mathcal L(Y_0).$$
--   This gives the deterministic product law for the random-clock admissibility argument.
-- source:
--   Atar, Mandelbaum and Reiman, https://arxiv.org/pdf/math/0407058#page=49, Appendix A.3, independent increments and stationary increments in the proof of Proposition 1

import Definitions.Def_ManyServerQED_Scheduling_PrimitiveCuts

open MeasureTheory ProbabilityTheory
open scoped NNReal
open ManyServerQED.Scheduling

theorem ManyServerQED.Scheduling.primitive_suffix_at_deterministic_cuts
    {Ω : Type*} [MeasurableSpace Ω] {k : ℕ} (M : SystemSequence Ω k)
    (n : ℕ) (d : Fin k → ℕ) (p q : Fin k → ℝ≥0) :
    IdentDistrib (primitiveSuffix M n d p q)
      (primitiveSuffix M n (fun _ => 0) (fun _ => 0) (fun _ => 0)) M.P M.P ∧
    Indep (primitivePrefixInfo M n d p q)
      (MeasurableSpace.comap (primitiveSuffix M n d p q) inferInstance) M.P := by sorry
