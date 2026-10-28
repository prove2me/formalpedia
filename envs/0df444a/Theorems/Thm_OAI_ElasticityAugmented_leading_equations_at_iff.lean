-- Prove2me | Theorems.Thm_OAI_ElasticityAugmented_leading_equations_at_iff
-- name    : OAI.ElasticityAugmented.leading_equations_at_iff
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T10:33:23.483661+00:00
-- url     : https://prove2.me/theorems/182fab8c-3095-4891-90ab-101e8702a9f5
-- title:
--   OAI.ElasticityAugmented.leading_equations_at_iff: intermediate lemma from OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Elasticity.global_uniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem*, OpenAI Math Release, September 24, 2026, result family 372, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ElasticityAugmented.leading_equations_at_iff` of [lean/OAI/MathematicalPhysics/Elasticity/ForcedTransport.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/ForcedTransport.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ElasticityAugmented`, with `open scoped BigOperators`):
--
--   ```lean
--   theorem leading_equations_at_iff (θ : Fin 3 → ℂ) (k r : Smooth)
--       (hr : ∀ x,(r : X → ℂ) x≠0) (hk : ∀ x,(k : X → ℂ) x≠0)
--       (hl : ∀ x,((k+r*r : Smooth) : X → ℂ) x≠0) (a : Fin 3 → Smooth) (b : Smooth) (x : X) :
--       ((∀ i,((leadingR coord θ (k-r*r) (r*r) a b i : Smooth) : X → ℂ) x=0) ∧
--         ((leadingS coord θ (k-r*r) (r*r) a b : Smooth) : X → ℂ) x=0) ↔
--       (∀ i,(direction (A := Smooth) coord θ (changeP r a i) : X → ℂ) x=
--         θ i*(changeS k r hr a b : X → ℂ) x) ∧
--       (direction (A := Smooth) coord θ (changeS k r hr a b) : X → ℂ) x=
--         ((transportT θ k r hk hl*changeS k r hr a b+
--           ∑ i,transportQ θ k r hr hk hl i*changeP r a i : Smooth) : X → ℂ) x
--   ```
--
--   **Definitions.** The statement is written with `OAI.ElasticityAugmented.Smooth`, `OAI.ElasticityAugmented.X`, `OAI.ElasticityAugmented.changeP`, `OAI.ElasticityAugmented.changeS`, `OAI.ElasticityAugmented.coord`, `OAI.ElasticityAugmented.direction`, `OAI.ElasticityAugmented.leadingR` and `OAI.ElasticityAugmented.leadingS` (definitions bundle `OAIQ6El000` of this split); `OAI.ElasticityAugmented.transportQ` and `OAI.ElasticityAugmented.transportT` (definitions bundle `OAIQ6El004` of this split).
--
--   **Used by.** The proofs of `OAI.ElasticityAugmented.exists_physical_leading_frame` and `OAI.Elasticity.dn_common_normal_frame` of this split import it.
-- source:
--   OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 372; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Uniqueness-for-the-Smooth-Isotropic-Elasticity-Inverse-Problem-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/ForcedTransport.lean (declaration OAI.ElasticityAugmented.leading_equations_at_iff)

import Mathlib
import Definitions.Def_OAIQ6El004

section

attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace ElasticityAugmented

theorem leading_equations_at_iff (θ : Fin 3 → ℂ) (k r : Smooth)
    (hr : ∀ x,(r : X → ℂ) x≠0) (hk : ∀ x,(k : X → ℂ) x≠0)
    (hl : ∀ x,((k+r*r : Smooth) : X → ℂ) x≠0) (a : Fin 3 → Smooth) (b : Smooth) (x : X) :
    ((∀ i,((leadingR coord θ (k-r*r) (r*r) a b i : Smooth) : X → ℂ) x=0) ∧
      ((leadingS coord θ (k-r*r) (r*r) a b : Smooth) : X → ℂ) x=0) ↔
    (∀ i,(direction (A := Smooth) coord θ (changeP r a i) : X → ℂ) x=
      θ i*(changeS k r hr a b : X → ℂ) x) ∧
    (direction (A := Smooth) coord θ (changeS k r hr a b) : X → ℂ) x=
      ((transportT θ k r hk hl*changeS k r hr a b+
        ∑ i,transportQ θ k r hr hk hl i*changeP r a i : Smooth) : X → ℂ) x := by
  sorry
end ElasticityAugmented

end
end

end OAI
end
