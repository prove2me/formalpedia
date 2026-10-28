-- Prove2me | Theorems.Thm_OAI_ElasticityAugmented_restricted_transports_of_chart_equal
-- name    : OAI.ElasticityAugmented.restricted_transports_of_chart_equal
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T10:45:04.615214+00:00
-- url     : https://prove2.me/theorems/f377e27d-cb9c-439c-9a6f-703addb747a5
-- title:
--   OAI.ElasticityAugmented.restricted_transports_of_chart_equal: intermediate lemma from OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Elasticity.global_uniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem*, OpenAI Math Release, September 24, 2026, result family 372, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ElasticityAugmented.restricted_transports_of_chart_equal` of [lean/OAI/MathematicalPhysics/Elasticity/Rigidity.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/Rigidity.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ElasticityAugmented`, with `open scoped BigOperators Matrix`, `open ElasticityConic`):
--
--   ```lean
--   theorem restricted_transports_of_chart_equal (m k : Fin 2 → X → ℝ)
--       (hm : ∀ q,ContDiff ℝ (⊤ : ℕ∞) (m q)) (hk : ∀ q,ContDiff ℝ (⊤ : ℕ∞) (k q))
--       (hmp : ∀ q x,0 < m q x) (hkp : ∀ q x,0 < k q x)
--       (he : ∀ b z,
--         chartMatrix b z
--           (transportT (chartTheta b z) (smoothOfReal (k 0) (hk 0)) (positiveRoot (m 0) (hm 0) (hmp 0))
--             (fun x => Complex.ofReal_ne_zero.mpr (hkp 0 x).ne') (real_sum_nonzero (m 0) (k 0) (hm 0) (hk 0) (hmp 0) (hkp 0)))
--           (transportQ (chartTheta b z) (smoothOfReal (k 0) (hk 0)) (positiveRoot (m 0) (hm 0) (hmp 0))
--             (positiveRoot_nonzero (m 0) (hm 0) (hmp 0)) (fun x => Complex.ofReal_ne_zero.mpr (hkp 0 x).ne')
--             (real_sum_nonzero (m 0) (k 0) (hm 0) (hk 0) (hmp 0) (hkp 0)))=
--         chartMatrix b z
--           (transportT (chartTheta b z) (smoothOfReal (k 1) (hk 1)) (positiveRoot (m 1) (hm 1) (hmp 1))
--             (fun x => Complex.ofReal_ne_zero.mpr (hkp 1 x).ne') (real_sum_nonzero (m 1) (k 1) (hm 1) (hk 1) (hmp 1) (hkp 1)))
--           (transportQ (chartTheta b z) (smoothOfReal (k 1) (hk 1)) (positiveRoot (m 1) (hm 1) (hmp 1))
--             (positiveRoot_nonzero (m 1) (hm 1) (hmp 1)) (fun x => Complex.ofReal_ne_zero.mpr (hkp 1 x).ne')
--             (real_sum_nonzero (m 1) (k 1) (hm 1) (hk 1) (hmp 1) (hkp 1)))) :
--       ElasticityRecovery.EqualRestrictedTransports (m 0) (k 0) (m 1) (k 1)
--   ```
--
--   **Definitions.** The statement is written with `OAI.ElasticityAugmented.Smooth` and `OAI.ElasticityAugmented.X` (definitions bundle `OAIQ6El000` of this split); `OAI.ElasticityConic.chartTheta` (definitions bundle `OAIQ6El002` of this split); `OAI.ElasticityAugmented.positiveRoot`, `OAI.ElasticityAugmented.positiveRoot_nonzero`, `OAI.ElasticityAugmented.real_sum_nonzero`, `OAI.ElasticityAugmented.smoothOfReal`, `OAI.ElasticityAugmented.transportQ`, `OAI.ElasticityAugmented.transportT` and `OAI.ElasticityConic.chartMatrix` (definitions bundle `OAIQ6El004` of this split); `OAI.ElasticityRecovery.EqualRestrictedTransports` (definitions bundle `OAIQ6El006` of this split).
--
--   **Used by.** The proof of `OAI.Elasticity.dn_global_coefficients_equal` of this split imports it.
-- source:
--   OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 372; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Uniqueness-for-the-Smooth-Isotropic-Elasticity-Inverse-Problem-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/Rigidity.lean (declaration OAI.ElasticityAugmented.restricted_transports_of_chart_equal)

import Mathlib
import Definitions.Def_OAIQ6El006

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Matrix
namespace ElasticityAugmented
open ElasticityConic
theorem restricted_transports_of_chart_equal (m k : Fin 2 → X → ℝ)
    (hm : ∀ q,ContDiff ℝ (⊤ : ℕ∞) (m q)) (hk : ∀ q,ContDiff ℝ (⊤ : ℕ∞) (k q))
    (hmp : ∀ q x,0 < m q x) (hkp : ∀ q x,0 < k q x)
    (he : ∀ b z,
      chartMatrix b z
        (transportT (chartTheta b z) (smoothOfReal (k 0) (hk 0)) (positiveRoot (m 0) (hm 0) (hmp 0))
          (fun x => Complex.ofReal_ne_zero.mpr (hkp 0 x).ne') (real_sum_nonzero (m 0) (k 0) (hm 0) (hk 0) (hmp 0) (hkp 0)))
        (transportQ (chartTheta b z) (smoothOfReal (k 0) (hk 0)) (positiveRoot (m 0) (hm 0) (hmp 0))
          (positiveRoot_nonzero (m 0) (hm 0) (hmp 0)) (fun x => Complex.ofReal_ne_zero.mpr (hkp 0 x).ne')
          (real_sum_nonzero (m 0) (k 0) (hm 0) (hk 0) (hmp 0) (hkp 0)))=
      chartMatrix b z
        (transportT (chartTheta b z) (smoothOfReal (k 1) (hk 1)) (positiveRoot (m 1) (hm 1) (hmp 1))
          (fun x => Complex.ofReal_ne_zero.mpr (hkp 1 x).ne') (real_sum_nonzero (m 1) (k 1) (hm 1) (hk 1) (hmp 1) (hkp 1)))
        (transportQ (chartTheta b z) (smoothOfReal (k 1) (hk 1)) (positiveRoot (m 1) (hm 1) (hmp 1))
          (positiveRoot_nonzero (m 1) (hm 1) (hmp 1)) (fun x => Complex.ofReal_ne_zero.mpr (hkp 1 x).ne')
          (real_sum_nonzero (m 1) (k 1) (hm 1) (hk 1) (hmp 1) (hkp 1)))) :
    ElasticityRecovery.EqualRestrictedTransports (m 0) (k 0) (m 1) (k 1) := by
  sorry
end ElasticityAugmented

end
end

end OAI
end
