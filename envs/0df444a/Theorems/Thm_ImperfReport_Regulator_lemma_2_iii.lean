-- Prove2me | Theorems.Thm_ImperfReport_Regulator_lemma_2_iii
-- name    : ImperfReport.Regulator.lemma_2_iii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:17:21.429369+00:00
-- url     : https://prove2.me/theorems/f373c481-f263-4bda-916b-19af39f09138
-- title:
--   Lemma 2 (iii): the firm's response to perfect reports at a low threshold
-- statement:
--   Suppose the payoff threshold satisfies $0<k<\beta$. Under perfectly informative mandatory reports $(\hat\alpha_G,\hat\alpha_B)=(1,0)$, the firm's greatest probability-maximizing information choice is exactly $q^\dagger(k)$. Its disclosure cutoff equals $k$, and its information probability is strictly below one:
--
--   $$q=q^\dagger(k)<1,\qquad t^\dagger(q)=k.$$
--
--   This identifies the benchmark response against which the conservative reporting system is compared. **Formalization Note** Only case (iii) of the source lemma is posed; the appendix's displayed closed form for $q$ is specialized to a uniform law.
-- source:
--   Friedman, Hughes, Michaeli, A Rationale for Imperfect Reporting Standards, SSRN 3636995 (version of November 24, 2020), p. 16, Lemma 2 (iii); pp. 33–34, proof

import Definitions.Def_ImperfReport_Regulator_Report

set_option autoImplicit false
open MeasureTheory Set

namespace ImperfReport.Regulator

/-- Friedman, Hughes, Michaeli, *A Rationale for Imperfect Reporting Standards*,
SSRN 3636995 (version of November 24, 2020), p. 16, Lemma 2 (iii).
Only the low-threshold case used in Proposition 1 is stated. Formalization
Note: the paper's appendix substitutes the uniform-law formula for `q†`; here
the inverse cutoff formula is used for the law `mu` in the model. -/
theorem lemma_2_iii (M : Model) (hM : M.Standing)
    (hk0 : 0 < M.k) (hkb : M.k < beta M) :
    (∀ q : ℝ, FirmBR M perfect q ↔ q = qdag M M.k) ∧
    tdag M (qdag M M.k) = M.k ∧ qdag M M.k < 1 := by sorry

end ImperfReport.Regulator
