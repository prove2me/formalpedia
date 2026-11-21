-- Prove2me | Theorems.Thm_JardenShami_sim_witness_mono_and_equivalence
-- name    : JardenShami.sim_witness_mono_and_equivalence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:43:16.562461+00:00
-- url     : https://prove2.me/theorems/429ca03e-43ea-4844-969c-1729032e56f8
-- title:
--   Jarden Shami: sim witness mono and equivalence
-- statement:
--   **Remark 7.2** (Section 7, `\label{remark 7.2}`). Under the standing assumption of Subsection
--   7.1, except `μ < κ`, which is not needed and is not assumed here (`κ` regular,
--   `C : [κ]^2 → μ` *-locally additive): if `β ≠ γ`, `α₁` witnesses `β ∼ γ` and `α₁ < α₂`, then
--   `α₂` witnesses `β ∼ γ` as well. Hence `∼` is an equivalence relation.
--
--   Source: https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section7.lean#L92-L122
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section7.lean#L92-L122

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section6
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section7
set_option autoImplicit true
open Cardinal
universe v w
noncomputable section
open JardenShami
open Tree

theorem JardenShami.sim_witness_mono_and_equivalence (κ μ : Cardinal.{w}) (hκ : κ.IsRegular)
    (C : Coloring (Kappa κ) (Kappa μ)) (hC : IsStarLocallyAdditive C) :
    (∀ (β γ α₁ α₂ : Kappa κ) (hβ : β < α₁) (hγ : γ < α₁) (h₁₂ : α₁ < α₂), β ≠ γ →
        C.color β α₁ hβ = C.color γ α₁ hγ →
          C.color β α₂ (hβ.trans h₁₂) = C.color γ α₂ (hγ.trans h₁₂)) ∧
      Equivalence (Sim C) := by sorry
