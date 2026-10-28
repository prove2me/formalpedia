-- Prove2me | Theorems.Thm_OAI_Lech_CharP_exists_length_with_module_limit
-- name    : OAI.Lech.CharP.exists_length_with_module_limit
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T20:20:54.925179+00:00
-- url     : https://prove2.me/theorems/9c76c48b-91ba-478c-9634-38c5f247e314
-- title:
--   OAI.Lech.CharP.exists_length_with_module_limit: intermediate lemma from OpenAI, Lech's multiplicity conjecture (result family 194)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Lech.dutta_domain`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Lech's multiplicity conjecture (result family 194)*, OpenAI Math Release, September 23, 2026, result family 194, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Lech.CharP`, with `open CategoryTheory`, `open scoped TensorProduct`, `open Lech.RootTower Lech.PerfectDomainStages Lech.Koszul IsLocalRing Filter`, `open scoped ENNReal Topology nonZeroDivisors`):
--
--   ```lean
--   theorem exists_length_with_module_limit (hh : 0 < Lech.dimension D) :
--       ∃ ell : Lech.AllModuleLength (PerfectClosure D p),
--         (∀ (M : ModuleCat.{u} D), IsFiniteLength D M →
--           Tendsto (fun n : ℕ => ((p : ℝ≥0∞)^(n*Lech.dimension D))⁻¹ *
--             (Module.length D (Lech.FrobeniusModule D p n M)).toENNReal)
--             atTop (𝓝 (ell.value ((ModuleCat.extendScalars (PerfectClosure.of D p)).obj M)))) ∧
--         (∀ (H : Ideal D), H.radical = maximalIdeal D →
--           Tendsto (fun n : ℕ => ((p : ℝ≥0∞)^(n*Lech.dimension D))⁻¹ *
--             (Module.length D (D ⧸ H.map (iterateFrobenius D p n))).toENNReal)
--             atTop (𝓝 (ell.value (ModuleCat.of (PerfectClosure D p)
--               ((PerfectClosure D p) ⧸ H.map (PerfectClosure.of D p)))))) ∧
--         (∀ (z : Fin (Lech.dimension D) → D),
--           (Ideal.span (Set.range z)).radical = maximalIdeal D →
--           ∀ a : ℕ, 0 < a →
--             ell.value (ModuleCat.of (PerfectClosure D p) ((PerfectClosure D p) ⧸
--               (parameterIdeal D z a).map (PerfectClosure.of D p))) =
--                 (a : ℝ≥0∞)^(Lech.dimension D) *
--                   ENNReal.ofReal (Lech.Primary.multiplicity (Ideal.span (Set.range z)))) ∧
--         (∀ (ys : List D), ys.length = Lech.dimension D →
--           (entryIdeal ys).radical = maximalIdeal D → ∀ i : ℤ, i < 0 →
--             ell.value ((unit (ys.map (PerfectClosure.of D p))).homology i) = 0) ∧
--         (∀ (z : Fin (Lech.dimension D) → D),
--           (Ideal.span (Set.range z)).radical = maximalIdeal D →
--             0 < Lech.Primary.multiplicity (Ideal.span (Set.range z)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Lech.AllModuleLength` (definitions bundle `OAIQ032L000` of this split); `OAI.Lech.CharP.parameterIdeal` (definitions bundle `OAIQ032L002` of this split); `OAI.Lech.FrobeniusModule` (definitions bundle `OAIQ032L004` of this split); `OAI.Lech.Koszul.entryIdeal` (definitions bundle `OAIQ032L005` of this split); `OAI.Lech.Primary.multiplicity` (definitions bundle `OAIQ032L006` of this split); `OAI.Lech.Koszul.unit` (definitions bundle `OAIQ032L014` of this split); `OAI.Lech.dimension` (the published bundle `Def_DuttaDomain`).
--
--   **Used by.** The proofs of `OAI.Lech.CharP.dutta_minimal_estimate` and `OAI.Lech.cyclicDuttaSequence_tendsto` of this split import it.
-- source:
--   OpenAI, Lech's multiplicity conjecture (result family 194), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 194; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Lechs-multiplicity-conjecture-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_DuttaDomain
import Definitions.Def_OAIQ032L014

section

attribute [-instance] _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace Lech.CharP
open Lech.RootTower Lech.PerfectDomainStages Lech.Koszul IsLocalRing Filter
open scoped ENNReal Topology nonZeroDivisors
universe u
variable (D : Type u) [CommRing D] [IsDomain D] [IsLocalRing D]
  [IsNoetherianRing D] [IsAdicComplete (maximalIdeal D) D]
  (p : ℕ) [Fact p.Prime] [CharP D p] [PerfectRing (ResidueField D) p]

theorem exists_length_with_module_limit (hh : 0 < Lech.dimension D) :
    ∃ ell : Lech.AllModuleLength (PerfectClosure D p),
      (∀ (M : ModuleCat.{u} D), IsFiniteLength D M →
        Tendsto (fun n : ℕ => ((p : ℝ≥0∞)^(n*Lech.dimension D))⁻¹ *
          (Module.length D (Lech.FrobeniusModule D p n M)).toENNReal)
          atTop (𝓝 (ell.value ((ModuleCat.extendScalars (PerfectClosure.of D p)).obj M)))) ∧
      (∀ (H : Ideal D), H.radical = maximalIdeal D →
        Tendsto (fun n : ℕ => ((p : ℝ≥0∞)^(n*Lech.dimension D))⁻¹ *
          (Module.length D (D ⧸ H.map (iterateFrobenius D p n))).toENNReal)
          atTop (𝓝 (ell.value (ModuleCat.of (PerfectClosure D p)
            ((PerfectClosure D p) ⧸ H.map (PerfectClosure.of D p)))))) ∧
      (∀ (z : Fin (Lech.dimension D) → D),
        (Ideal.span (Set.range z)).radical = maximalIdeal D →
        ∀ a : ℕ, 0 < a →
          ell.value (ModuleCat.of (PerfectClosure D p) ((PerfectClosure D p) ⧸
            (parameterIdeal D z a).map (PerfectClosure.of D p))) =
              (a : ℝ≥0∞)^(Lech.dimension D) *
                ENNReal.ofReal (Lech.Primary.multiplicity (Ideal.span (Set.range z)))) ∧
      (∀ (ys : List D), ys.length = Lech.dimension D →
        (entryIdeal ys).radical = maximalIdeal D → ∀ i : ℤ, i < 0 →
          ell.value ((unit (ys.map (PerfectClosure.of D p))).homology i) = 0) ∧
      (∀ (z : Fin (Lech.dimension D) → D),
        (Ideal.span (Set.range z)).radical = maximalIdeal D →
          0 < Lech.Primary.multiplicity (Ideal.span (Set.range z))) := by
  sorry
end Lech.CharP

end

end OAI
end
