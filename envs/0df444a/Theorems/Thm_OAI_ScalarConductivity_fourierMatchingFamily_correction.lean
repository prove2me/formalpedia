-- Prove2me | Theorems.Thm_OAI_ScalarConductivity_fourierMatchingFamily_correction
-- name    : OAI.ScalarConductivity.fourierMatchingFamily_correction
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T21:50:10.360081+00:00
-- url     : https://prove2.me/theorems/08d73cef-c3eb-4745-99ad-f5283a3b2c90
-- title:
--   OAI.ScalarConductivity.fourierMatchingFamily_correction: intermediate lemma from OpenAI, Nonuniqueness for bounded measurable scalar conductivities in three dimensions (result family 365)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ScalarConductivity.main_nonuniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness for bounded measurable scalar conductivities in three dimensions (result family 365)*, OpenAI Math Release, September 23, 2026, result family 365, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ScalarConductivity.fourierMatchingFamily_correction` of [lean/OAI/Analysis/Conductivity/Fourier/FourierMatchingFamilyCorrection.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Conductivity/Fourier/FourierMatchingFamilyCorrection.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ScalarConductivity`, with `open Set Filter Topology Real Matrix`, `open scoped Matrix.Norms.Elementwise`):
--
--   ```lean
--   lemma fourierMatchingFamily_correction {s : Fin 3 → ℝ}
--       (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
--       {k : ℤ} (hk : k≠0) {f g : ℝ×Coord3 → ℝ}
--       (hfs : ContDiff ℝ (↑(⊤:ℕ∞)) f) (hgs : ContDiff ℝ (↑(⊤:ℕ∞)) g)
--       (hfp : ∀ p,AngularPeriodic (2*Real.pi) (fun x => f (p,x)))
--       (hgp : ∀ p,AngularPeriodic (2*Real.pi) (fun x => g (p,x)))
--       (hfz : ∀ x,f (0,x)=0) (hgz : ∀ x,g (0,x)=0) {ε : ℝ} (hε : 0<ε) :
--       ∀ᶠ p in 𝓝 (0:ℝ),periodicSourceMoment (2*Real.pi) (fun y => fourierMatchingPair s k f g (p,y))
--         (fun j y => fourierMatchingResidual s k f g j (p,y))=0 →
--         ∃ H : Coord3 → Mat3,ContDiff ℝ (↑(⊤:ℕ∞)) H ∧ AngularPeriodic (2*Real.pi) H ∧
--           tsupport H⊆{x | x 0∈Icc (1/2) (11/2)} ∧ (∀ x,(H x).IsSymm) ∧
--           (∀ j,symmetricSource H (fun y => fourierMatchingPair s k f g (p,y)) j=(fun y => fourierMatchingResidual s k f g j (p,y))) ∧
--           ∀ x,‖H x‖≤ε
--   ```
--
--   **Definitions.** The statement is written with `OAI.ScalarConductivity.AngularPeriodic`, `OAI.ScalarConductivity.Coord3`, `OAI.ScalarConductivity.Mat3` and `OAI.ScalarConductivity.symmetricSource` (definitions bundle `OAIQ059C000` of this split); `OAI.ScalarConductivity.periodicSourceMoment` (definitions bundle `OAIQ059C005` of this split); `OAI.ScalarConductivity.fourierMatchingPair` and `OAI.ScalarConductivity.fourierMatchingResidual` (definitions bundle `OAIQ059C007` of this split).
--
--   **Used by.** The proof of `OAI.ScalarConductivity.elliptic_fourier_matching_regular` of this split imports it.
-- source:
--   OpenAI, Nonuniqueness for bounded measurable scalar conductivities in three dimensions (result family 365), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 365; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-for-Bounded-Measurable-Scalar-Conductivities-in-Three-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Conductivity/Fourier/FourierMatchingFamilyCorrection.lean (declaration OAI.ScalarConductivity.fourierMatchingFamily_correction)

import Mathlib
import Definitions.Def_OAIQ059C007

section

attribute [-instance] _root_.OAI.ScalarConductivity.instBorelSpaceSymmetric3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real Matrix
open scoped Matrix.Norms.Elementwise

lemma fourierMatchingFamily_correction {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {k : ℤ} (hk : k≠0) {f g : ℝ×Coord3 → ℝ}
    (hfs : ContDiff ℝ (↑(⊤:ℕ∞)) f) (hgs : ContDiff ℝ (↑(⊤:ℕ∞)) g)
    (hfp : ∀ p,AngularPeriodic (2*Real.pi) (fun x => f (p,x)))
    (hgp : ∀ p,AngularPeriodic (2*Real.pi) (fun x => g (p,x)))
    (hfz : ∀ x,f (0,x)=0) (hgz : ∀ x,g (0,x)=0) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ p in 𝓝 (0:ℝ),periodicSourceMoment (2*Real.pi) (fun y => fourierMatchingPair s k f g (p,y))
      (fun j y => fourierMatchingResidual s k f g j (p,y))=0 →
      ∃ H : Coord3 → Mat3,ContDiff ℝ (↑(⊤:ℕ∞)) H ∧ AngularPeriodic (2*Real.pi) H ∧
        tsupport H⊆{x | x 0∈Icc (1/2) (11/2)} ∧ (∀ x,(H x).IsSymm) ∧
        (∀ j,symmetricSource H (fun y => fourierMatchingPair s k f g (p,y)) j=(fun y => fourierMatchingResidual s k f g j (p,y))) ∧
        ∀ x,‖H x‖≤ε := by
  sorry

end ScalarConductivity

end
end

end OAI
end
