-- Prove2me | Theorems.Thm_OAI_ScalarConductivity_elliptic_fourier_matching_regular
-- name    : OAI.ScalarConductivity.elliptic_fourier_matching_regular
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T21:43:38.517119+00:00
-- url     : https://prove2.me/theorems/272833ba-7cf5-4200-94ce-a0298812b18b
-- title:
--   OAI.ScalarConductivity.elliptic_fourier_matching_regular: intermediate lemma from OpenAI, Nonuniqueness for bounded measurable scalar conductivities in three dimensions (result family 365)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ScalarConductivity.main_nonuniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness for bounded measurable scalar conductivities in three dimensions (result family 365)*, OpenAI Math Release, September 23, 2026, result family 365, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ScalarConductivity.elliptic_fourier_matching_regular` of [lean/OAI/Analysis/Conductivity/Fourier/PeriodicBandCompactness.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Conductivity/Fourier/PeriodicBandCompactness.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ScalarConductivity`, with `open Set Filter Topology Real Matrix MeasureTheory`, `open scoped Matrix.Norms.Elementwise`):
--
--   ```lean
--   theorem elliptic_fourier_matching_regular {s : Fin 3 → ℝ}
--       (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
--       {k : ℤ} (hk : k≠0) {a b pa pb : (Fin 2 → ℤ) → ℝ} {A B ga gb : ℝ}
--       (hA : 0≤A) (hB : 0≤B) (ha : ∀ h,|a h|≤A) (hb : ∀ h,|b h|≤B)
--       (hga : 0<ga) (hgb : 0<gb)
--       (hra : ∀ h,a h≠0 → ga≤torusRate s h)
--       (hrb : ∀ h,b h≠0 → torusRate s ![0,k]+gb≤torusRate s h)
--       (hpb : pb ![0,k]=0) {δ : ℝ} (hδ : 0<δ) :
--       ∃ p : ℝ,p∈Ioc 0 (1/2) ∧ p<δ ∧
--         ∃ (u : Coord3 → Fin 2 → ℝ) (D : Coord3 → Mat3),
--           ContDiff ℝ (↑(⊤:ℕ∞)) u ∧ ContDiff ℝ (↑(⊤:ℕ∞)) D ∧
--           AngularPeriodic (2*Real.pi) u ∧ AngularPeriodic (2*Real.pi) D ∧
--           (∀ x,(D x).IsSymm) ∧
--           (∀ x v,(1/4)*(v ⬝ᵥ v)≤v ⬝ᵥ (D x*ᵥv) ∧
--             v ⬝ᵥ (D x*ᵥv)≤(3*‖flatBackgroundTensor s‖+1)*(v ⬝ᵥ v)) ∧
--           (∀ j x,0<x 0 → symmetricSource D u j x=0) ∧
--           (∀ x,x 0∉Icc (1/2) (11/2) → D x=flatBackgroundTensor s) ∧
--           (∀ x,x 0∈Icc 0 (1/2) → u x=
--             ![x 0+flatFourier s (normalizedFourierCoefficients s 0 (10+1/p) a) pa x,
--               flatPhaseMode s ![0,k] 0 x+
--                 flatFourier s (normalizedFourierCoefficients s (torusRate s ![0,k]) (10+1/p) b) pb x]) ∧
--           (∀ x,4≤x 0 → u x=![x 0,flatPhaseMode s ![0,k] 0 x]) ∧
--           ∀ᵐ x : Coord3,x 0∈Ioo 0 6 → LinearIndependent ℝ (gradientColumns (fderiv ℝ u x)).col
--   ```
--
--   **Definitions.** The statement is written with `OAI.ScalarConductivity.AngularPeriodic`, `OAI.ScalarConductivity.Coord3`, `OAI.ScalarConductivity.Mat3`, `OAI.ScalarConductivity.gradientColumns`, `OAI.ScalarConductivity.symmetricSource` and `OAI.ScalarConductivity.torusRate` (definitions bundle `OAIQ059C000` of this split); `OAI.ScalarConductivity.flatBackgroundTensor` (definitions bundle `OAIQ059C003` of this split); `OAI.ScalarConductivity.flatFourier` and `OAI.ScalarConductivity.flatPhaseMode` (definitions bundle `OAIQ059C004` of this split); `OAI.ScalarConductivity.normalizedFourierCoefficients` (definitions bundle `OAIQ059C005` of this split).
--
--   **Used by.** The proof of `OAI.ScalarConductivity.physicalFiniteEndingData_nonempty` of this split imports it.
-- source:
--   OpenAI, Nonuniqueness for bounded measurable scalar conductivities in three dimensions (result family 365), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 365; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-for-Bounded-Measurable-Scalar-Conductivities-in-Three-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Conductivity/Fourier/PeriodicBandCompactness.lean (declaration OAI.ScalarConductivity.elliptic_fourier_matching_regular)

import Mathlib
import Definitions.Def_OAIQ059C003
import Definitions.Def_OAIQ059C004
import Definitions.Def_OAIQ059C005

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity
open Set Filter Topology Real Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

theorem elliptic_fourier_matching_regular {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {k : ℤ} (hk : k≠0) {a b pa pb : (Fin 2 → ℤ) → ℝ} {A B ga gb : ℝ}
    (hA : 0≤A) (hB : 0≤B) (ha : ∀ h,|a h|≤A) (hb : ∀ h,|b h|≤B)
    (hga : 0<ga) (hgb : 0<gb)
    (hra : ∀ h,a h≠0 → ga≤torusRate s h)
    (hrb : ∀ h,b h≠0 → torusRate s ![0,k]+gb≤torusRate s h)
    (hpb : pb ![0,k]=0) {δ : ℝ} (hδ : 0<δ) :
    ∃ p : ℝ,p∈Ioc 0 (1/2) ∧ p<δ ∧
      ∃ (u : Coord3 → Fin 2 → ℝ) (D : Coord3 → Mat3),
        ContDiff ℝ (↑(⊤:ℕ∞)) u ∧ ContDiff ℝ (↑(⊤:ℕ∞)) D ∧
        AngularPeriodic (2*Real.pi) u ∧ AngularPeriodic (2*Real.pi) D ∧
        (∀ x,(D x).IsSymm) ∧
        (∀ x v,(1/4)*(v ⬝ᵥ v)≤v ⬝ᵥ (D x*ᵥv) ∧
          v ⬝ᵥ (D x*ᵥv)≤(3*‖flatBackgroundTensor s‖+1)*(v ⬝ᵥ v)) ∧
        (∀ j x,0<x 0 → symmetricSource D u j x=0) ∧
        (∀ x,x 0∉Icc (1/2) (11/2) → D x=flatBackgroundTensor s) ∧
        (∀ x,x 0∈Icc 0 (1/2) → u x=
          ![x 0+flatFourier s (normalizedFourierCoefficients s 0 (10+1/p) a) pa x,
            flatPhaseMode s ![0,k] 0 x+
              flatFourier s (normalizedFourierCoefficients s (torusRate s ![0,k]) (10+1/p) b) pb x]) ∧
        (∀ x,4≤x 0 → u x=![x 0,flatPhaseMode s ![0,k] 0 x]) ∧
        ∀ᵐ x : Coord3,x 0∈Ioo 0 6 → LinearIndependent ℝ (gradientColumns (fderiv ℝ u x)).col := by
  sorry

end ScalarConductivity

end

end OAI
end
