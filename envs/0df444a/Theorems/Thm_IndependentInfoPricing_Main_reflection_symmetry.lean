-- Prove2me | Theorems.Thm_IndependentInfoPricing_Main_reflection_symmetry
-- name    : IndependentInfoPricing.Main.reflection_symmetry
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:34:08.448276+00:00
-- url     : https://prove2.me/theorems/868b975f-b449-4ac2-a2ac-cce1873882d9
-- title:
--   Lemma 4.8 — Reflection symmetry
-- statement:
--   Reflect values, allocations and payments by $(v,x,p)\mapsto(-v,1-x,p)$. For any report domain $T$, a direct additive mechanism is feasible on $T$ if and only if its reflected mechanism is feasible on $-T$. Applying this transformation twice is the identity and the payment at corresponding reports is unchanged. In particular this supplies the bijection between the two open half-spaces in Lemma 4.8.
--
--   For every product probability law, global reflection preserves $\operatorname{OPT}^{\rm rel}$, priced full revelation, $R$ and $\widetilde R$, and exchanges activation with deactivation benchmarks:
--
--   $$\operatorname{SRev}^{+}(-F)=\operatorname{SRev}^{-}(F),\qquad \operatorname{SRev}^{-}(-F)=\operatorname{SRev}^{+}(F).$$
--
--   These are global distribution identities. No price vector is selected after the realized sign pattern is observed.
--
--   Differences from the source:
--   - generalization: reflection bijection on the two half-spaces, with the global use in Section 4.5.1 → reflection iff and involution on every report domain, together with the global benchmark identities; reason: taking the negative half-space recovers Lemma 4.8 and taking the full domain recovers the global reflection used by the source
--   - encoding: real expected revenues and independent coordinates indexed by [Q] → nonnegative extended integrals and suprema with coordinates indexed by Fin Q; reason: preserves arbitrary real product laws and infinite revenues without default-zero integration; Fin Q only relabels the finite states
-- source:
--   Hu Fu, Chenshuo Guo, STOC 2027 submission #1459 (October 2026), Lemma 4.8, printed pp.31–31 (PDF pp.33–33); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1459.pdf

import Definitions.Def_IndependentInfoPricing_Main_Analysis

open MeasureTheory
open scoped BigOperators ENNReal
noncomputable section

namespace IndependentInfoPricing.Main

/-- Lemma 4.8, pp.31–32 (PDF 33–34), extended to any report domain as in §4.5.1. -/
theorem reflection_symmetry {Q : ℕ} (T : Set (Values (Fin Q)))
    (m : DirectMechanism (Fin Q)) (F : Marginals (Fin Q)) (hF : ProbabilityMarginals F) :
    (RelaxedOn T m ↔ RelaxedOn (reflectDomain T) (reflectMechanism m)) ∧
    reflectMechanism (reflectMechanism m) = m ∧
    (∀ v, (reflectMechanism m).price (-v) = m.price v) ∧
    optRel (productLaw (reflectedMarginals F)) = optRel (productLaw F) ∧
    sRevPlus (productLaw (reflectedMarginals F)) = sRevMinus (productLaw F) ∧
    sRevMinus (productLaw (reflectedMarginals F)) = sRevPlus (productLaw F) ∧
    fullRev (productLaw (reflectedMarginals F)) = fullRev (productLaw F) ∧
    benchmark (productLaw (reflectedMarginals F)) = benchmark (productLaw F) ∧
    benchmarkSym (productLaw (reflectedMarginals F)) = benchmarkSym (productLaw F) := by sorry

end IndependentInfoPricing.Main
