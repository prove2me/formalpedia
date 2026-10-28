-- Prove2me | Theorems.Thm_OAI_ElasticityAugmented_forced_equations_at
-- name    : OAI.ElasticityAugmented.forced_equations_at
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T10:34:06.084707+00:00
-- url     : https://prove2.me/theorems/39d11671-9432-47e0-a81f-1371f82cdcbe
-- title:
--   OAI.ElasticityAugmented.forced_equations_at: intermediate lemma from OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Elasticity.global_uniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem*, OpenAI Math Release, September 24, 2026, result family 372, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ElasticityAugmented.forced_equations_at` of [lean/OAI/MathematicalPhysics/Elasticity/ForcedTransport.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/ForcedTransport.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ElasticityAugmented`, with `open scoped BigOperators`):
--
--   ```lean
--   lemma forced_equations_at (θ : Fin 3 → ℂ) (k r : Smooth)
--       (hr : ∀ x,(r : X → ℂ) x≠0) (hk : ∀ x,(k : X → ℂ) x≠0)
--       (hl : ∀ x,((k+r*r : Smooth) : X → ℂ) x≠0)
--       (H : Fin 3 → Smooth) (K : Smooth) (a : Fin 3 → Smooth) (b : Smooth) (x : X)
--       (hp : ∀ i,(direction (A := Smooth) coord θ (changeP r a i) : X → ℂ) x=
--         θ i*(changeS k r hr a b : X → ℂ) x+(topSource r hr H i : X → ℂ) x)
--       (hs : (direction (A := Smooth) coord θ (changeS k r hr a b) : X → ℂ) x=
--         ((transportT θ k r hk hl*changeS k r hr a b+
--           ∑ i,transportQ θ k r hr hk hl i*changeP r a i : Smooth) : X → ℂ) x+
--             (scalarSource k r hr hl H K : X → ℂ) x) :
--       (∀ i,((leadingR coord θ (k-r*r) (r*r) a b i : Smooth) : X → ℂ) x=(H i : X → ℂ) x) ∧
--         ((leadingS coord θ (k-r*r) (r*r) a b : Smooth) : X → ℂ) x=(K : X → ℂ) x
--   ```
--
--   **Definitions.** The statement is written with `OAI.ElasticityAugmented.Smooth`, `OAI.ElasticityAugmented.X`, `OAI.ElasticityAugmented.changeP`, `OAI.ElasticityAugmented.changeS`, `OAI.ElasticityAugmented.coord`, `OAI.ElasticityAugmented.direction`, `OAI.ElasticityAugmented.leadingR` and `OAI.ElasticityAugmented.leadingS` (definitions bundle `OAIQ6El000` of this split); `OAI.ElasticityAugmented.scalarSource`, `OAI.ElasticityAugmented.topSource`, `OAI.ElasticityAugmented.transportQ` and `OAI.ElasticityAugmented.transportT` (definitions bundle `OAIQ6El004` of this split).
--
--   **Used by.** The proof of `OAI.ElasticityAugmented.exists_physical_forced_transport` of this split imports it.
-- source:
--   OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 372; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Uniqueness-for-the-Smooth-Isotropic-Elasticity-Inverse-Problem-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/ForcedTransport.lean (declaration OAI.ElasticityAugmented.forced_equations_at)

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

lemma forced_equations_at (θ : Fin 3 → ℂ) (k r : Smooth)
    (hr : ∀ x,(r : X → ℂ) x≠0) (hk : ∀ x,(k : X → ℂ) x≠0)
    (hl : ∀ x,((k+r*r : Smooth) : X → ℂ) x≠0)
    (H : Fin 3 → Smooth) (K : Smooth) (a : Fin 3 → Smooth) (b : Smooth) (x : X)
    (hp : ∀ i,(direction (A := Smooth) coord θ (changeP r a i) : X → ℂ) x=
      θ i*(changeS k r hr a b : X → ℂ) x+(topSource r hr H i : X → ℂ) x)
    (hs : (direction (A := Smooth) coord θ (changeS k r hr a b) : X → ℂ) x=
      ((transportT θ k r hk hl*changeS k r hr a b+
        ∑ i,transportQ θ k r hr hk hl i*changeP r a i : Smooth) : X → ℂ) x+
          (scalarSource k r hr hl H K : X → ℂ) x) :
    (∀ i,((leadingR coord θ (k-r*r) (r*r) a b i : Smooth) : X → ℂ) x=(H i : X → ℂ) x) ∧
      ((leadingS coord θ (k-r*r) (r*r) a b : Smooth) : X → ℂ) x=(K : X → ℂ) x := by
  sorry
end ElasticityAugmented

end
end

end OAI
end
