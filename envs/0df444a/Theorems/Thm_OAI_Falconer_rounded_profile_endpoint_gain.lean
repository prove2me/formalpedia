-- Prove2me | Theorems.Thm_OAI_Falconer_rounded_profile_endpoint_gain
-- name    : OAI.Falconer.rounded_profile_endpoint_gain
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T21:54:52.176109+00:00
-- url     : https://prove2.me/theorems/245d65d5-82a1-4fab-b4dc-8342ca30c308
-- title:
--   OAI.Falconer.rounded_profile_endpoint_gain: intermediate lemma from OpenAI, The Falconer distance conjecture in all dimensions (result family 073)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Falconer.falconer_distance_conjecture`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Falconer distance conjecture in all dimensions (result family 073)*, OpenAI Math Release, September 23, 2026, result family 73, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Falconer.rounded_profile_endpoint_gain` of [lean/OAI/MeasureTheory/Falconer/Estimates/RoundedEndpointGain.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Estimates/RoundedEndpointGain.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Falconer`, with `open Set Regularization`):
--
--   ```lean
--   theorem rounded_profile_endpoint_gain {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1/100) :
--       ∃ eg η : ℝ, ∃ Ng : ℕ, 0 < eg ∧ eg ≤ 1 ∧ 0 < η ∧ 0 < Ng ∧
--       ∀ m B : ℕ, 0 < m → 0 < B → Even B →
--       ∀ L : Finset (CellPath 2), L ⊆ cubePaths 2 (m*B) →
--       ∀ (f : CellPath 2 → List ℕ) (p : CellPath 2) (Q : DyadicCube 2), Q.side = 1 →
--       ∀ s t α τ β lam χ r ζ : ℝ, κ ≤ s → s ≤ 1-8*κ → 0 ≤ α → 0 < τ → 0 < β → 0 < lam →
--       ∀ J : ℕ, ∀ S : List (ℝ × ℝ),
--         (let N := m*B;
--          let g := fun x => regularizedProfile L (blockLabel L N B f (m+1)) N B (m+1) p ((N:ℝ)*x);
--          StructuredProfilePieces g τ α (s+κ) 1 S) →
--         (let N := m*B;
--          let g := fun x => regularizedProfile L (blockLabel L N B f (m+1)) N B (m+1) p ((N:ℝ)*x);
--          t-lam ≤ g 1) →
--         1-χ ≤ (S.map Prod.snd).sum → s+8*κ ≤ t → lam+2*χ ≤ κ →
--         2/(m:ℝ) ≤ τ/2 → 4/(m:ℝ) ≤ α*(τ/2) → 16/((m:ℝ)*τ) ≤ κ/2 →
--         (2/(m:ℝ))*(S.length:ℝ) ≤ r → r ≤ κ → S.length ≤ J →
--         4*(Ng:ℝ) ≤ τ*(m*B:ℕ) → 4*β ≤ eg*τ/8 → 3*α ≤ eg/4 →
--         s+ζ+β ≤ s*(1-χ-r)+η*κ-9*α-13*β*(J:ℝ) →
--         (let N := m*B;
--          let H : ℝ := (4*(N+2)+11:ℕ);
--          let G := (2:ℝ)^(3*(m+1))*((2*B+1:ℕ):ℝ)^(m+1);
--          let W := profileBudgetSequence H G ((2:ℝ)^(lam*(N:ℝ)));
--          (∀ j ≤ 2*J, ∀ A : ℝ,
--            profileGeometryConstant (m+1) B (W j) A ≤ (2:ℝ)^((4*β)*(N:ℝ)+A)) ∧
--          640*((N:ℝ)+3) ≤ (2:ℝ)^(β*(N:ℝ)) ∧
--          (43264*H^4)^(2*J) ≤ (2:ℝ)^(β*(N:ℝ))) →
--         ProfileEndpointBound (m*B) B (m+1) L f p Q m 0 s ((2:ℝ)^(lam*(m*B:ℕ)))
--           ((2:ℝ)^((s+ζ)*(m*B:ℕ)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Falconer.DyadicCube`, `OAI.Falconer.cubePaths` and `OAI.Falconer.Regularization.CellPath` (definitions bundle `OAIQ088F000` of this split); `OAI.Falconer.StructuredProfilePieces`, `OAI.Falconer.profileBudgetSequence` and `OAI.Falconer.profileGeometryConstant` (definitions bundle `OAIQ088F001` of this split); `OAI.Falconer.ProfileEndpointBound`, `OAI.Falconer.Regularization.blockLabel` and `OAI.Falconer.Regularization.regularizedProfile` (definitions bundle `OAIQ088F002` of this split).
--
--   **Used by.** The proof of `OAI.Falconer.publishedPlanarFurstenberg_proved` of this split imports it.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions (result family 073), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 73; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Estimates/RoundedEndpointGain.lean (declaration OAI.Falconer.rounded_profile_endpoint_gain)

import Mathlib
import Definitions.Def_OAIQ088F002

section

attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Falconer
open Set Regularization

theorem rounded_profile_endpoint_gain {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1/100) :
    ∃ eg η : ℝ, ∃ Ng : ℕ, 0 < eg ∧ eg ≤ 1 ∧ 0 < η ∧ 0 < Ng ∧
    ∀ m B : ℕ, 0 < m → 0 < B → Even B →
    ∀ L : Finset (CellPath 2), L ⊆ cubePaths 2 (m*B) →
    ∀ (f : CellPath 2 → List ℕ) (p : CellPath 2) (Q : DyadicCube 2), Q.side = 1 →
    ∀ s t α τ β lam χ r ζ : ℝ, κ ≤ s → s ≤ 1-8*κ → 0 ≤ α → 0 < τ → 0 < β → 0 < lam →
    ∀ J : ℕ, ∀ S : List (ℝ × ℝ),
      (let N := m*B;
       let g := fun x => regularizedProfile L (blockLabel L N B f (m+1)) N B (m+1) p ((N:ℝ)*x);
       StructuredProfilePieces g τ α (s+κ) 1 S) →
      (let N := m*B;
       let g := fun x => regularizedProfile L (blockLabel L N B f (m+1)) N B (m+1) p ((N:ℝ)*x);
       t-lam ≤ g 1) →
      1-χ ≤ (S.map Prod.snd).sum → s+8*κ ≤ t → lam+2*χ ≤ κ →
      2/(m:ℝ) ≤ τ/2 → 4/(m:ℝ) ≤ α*(τ/2) → 16/((m:ℝ)*τ) ≤ κ/2 →
      (2/(m:ℝ))*(S.length:ℝ) ≤ r → r ≤ κ → S.length ≤ J →
      4*(Ng:ℝ) ≤ τ*(m*B:ℕ) → 4*β ≤ eg*τ/8 → 3*α ≤ eg/4 →
      s+ζ+β ≤ s*(1-χ-r)+η*κ-9*α-13*β*(J:ℝ) →
      (let N := m*B;
       let H : ℝ := (4*(N+2)+11:ℕ);
       let G := (2:ℝ)^(3*(m+1))*((2*B+1:ℕ):ℝ)^(m+1);
       let W := profileBudgetSequence H G ((2:ℝ)^(lam*(N:ℝ)));
       (∀ j ≤ 2*J, ∀ A : ℝ,
         profileGeometryConstant (m+1) B (W j) A ≤ (2:ℝ)^((4*β)*(N:ℝ)+A)) ∧
       640*((N:ℝ)+3) ≤ (2:ℝ)^(β*(N:ℝ)) ∧
       (43264*H^4)^(2*J) ≤ (2:ℝ)^(β*(N:ℝ))) →
      ProfileEndpointBound (m*B) B (m+1) L f p Q m 0 s ((2:ℝ)^(lam*(m*B:ℕ)))
        ((2:ℝ)^((s+ζ)*(m*B:ℕ))) := by
  sorry

end Falconer

end OAI
end
