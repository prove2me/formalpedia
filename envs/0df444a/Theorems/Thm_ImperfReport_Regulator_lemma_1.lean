-- Prove2me | Theorems.Thm_ImperfReport_Regulator_lemma_1
-- name    : ImperfReport.Regulator.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:16:40.799369+00:00
-- url     : https://prove2.me/theorems/efe9344b-8876-4411-b039-486eca04e3d5
-- title:
--   Lemma 1: existence and monotonicity of the disclosure cutoff
-- statement:
--   Let $\omega_2$ have the atomless full-support law of the model, mean $\beta$ and CDF $F$. For every information-acquisition probability $q\in[0,1]$, there is a unique Bayes-consistent nondisclosure cutoff $t^\dagger(q)\in[0,\beta]$, satisfying
--
--   $$ (1-q)(\beta-t^\dagger(q))=q\int_0^{t^\dagger(q)}F(x)\,dx. $$
--
--   The cutoff lies in $(0,\beta)$ for $0<q<1$ and is strictly decreasing throughout $[0,1]$. Thus the firm's disclosure threshold is independent of the mandatory report and is invertible in $q$. **Formalization Note** At $q=0$ the cutoff is $\beta$, and at $q=1$ it is zero; the open interval printed in Lemma 1 cannot cover those endpoints.
-- source:
--   Friedman, Hughes, Michaeli, A Rationale for Imperfect Reporting Standards, SSRN 3636995 (version of November 24, 2020), p. 15, Lemma 1; p. 33, proof

import Definitions.Def_ImperfReport_Regulator_Model

set_option autoImplicit false
open MeasureTheory Set

namespace ImperfReport.Regulator

/-- Friedman, Hughes, Michaeli, *A Rationale for Imperfect Reporting Standards*,
SSRN 3636995 (version of November 24, 2020), p. 15, Lemma 1.
Formalization Note: the cutoff is interior only for `0 < q < 1`; its boundary
values are `β` at `q = 0` and `0` at `q = 1`. The paper's displayed open
interval fails at those endpoints. The atomless full-support law replaces the
density and ensures uniqueness; the appendix proof on p. 33 uses a uniform law. -/
theorem lemma_1 (M : Model) (hM : M.Standing) :
    (∀ q ∈ Set.Icc (0 : ℝ) 1,
      (∃! t, IsCutoff M q t) ∧
      IsCutoff M q (tdag M q) ∧
      tdag M q ∈ Set.Icc 0 (beta M) ∧
      (1 - q) * (beta M - tdag M q) =
        q * (∫ x in (0)..(tdag M q), F M x)) ∧
    (∀ q ∈ Set.Ioo (0 : ℝ) 1, tdag M q ∈ Set.Ioo 0 (beta M)) ∧
    StrictAntiOn (tdag M) (Set.Icc (0 : ℝ) 1) := by sorry

end ImperfReport.Regulator
