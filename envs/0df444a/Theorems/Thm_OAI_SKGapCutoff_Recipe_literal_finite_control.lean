-- Prove2me | Theorems.Thm_OAI_SKGapCutoff_Recipe_literal_finite_control
-- name    : OAI.SKGapCutoff.Recipe.literal_finite_control
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:30:28.385304+00:00
-- url     : https://prove2.me/theorems/b68b045e-4927-4bfd-bb39-d169327440c5
-- title:
--   OAI.SKGapCutoff.Recipe.literal_finite_control: intermediate lemma from OpenAI, A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SKGap.sk_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227)*, OpenAI Math Release, September 24, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SKGapCutoff.Recipe.literal_finite_control` of [lean/OAI/Probability/SKGap/Localization/LiteralLocalInput.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SKGap/Localization/LiteralLocalInput.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SKGapCutoff.Recipe`, with `open scoped BigOperators Matrix.Norms.Frobenius`, `open Primary Static SKGap.Stein SKGap.Noncrossing.Primary SKGap.Noncrossing.Primary.Tensor.Series SKGap.Noncrossing.ClosedMarked`):
--
--   ```lean
--   theorem literal_finite_control (j : ℝ) (J : ∀b,Interaction (n b))
--       (h : ∀b,Fin (n b)→ℝ) (l : Fin M) (f : KernelExpr)
--       (a c : ∀b,Spin (n b)→ℝ) (r e : ∀b,Fin (n b)→ℝ)
--       (w y : ∀b,VectorFields (n b)) (E : ∀b,Set (Spin (n b)))
--       (hn : ∀b,0<n b) (he : ∀b,vectorNorm (e b)≤1)
--       {K B R Bc Va Vc A V S F W C : ℝ}
--       (hK : 0≤K) (hB : 0≤B) (hBc : 0≤Bc) (hVa : 0≤Va) (hVc : 0≤Vc)
--       (hA : 1≤A) (hV : 0≤V) (hS : 0≤S) (hF : 0≤F) (hW : 0≤W) (hC : 0≤C)
--       (hop : ∀b,SKGap.opNorm (J b)≤K)
--       (hformal : ∀b x,∀q<M,ShapeBound (formalField j (J b) (h b) x q) B)
--       (ha : ∀b x,x∈flipNeighborhood (flipNeighborhood (E b))→|a b x|≤R)
--       (hc : ∀b x,x∈flipNeighborhood (flipNeighborhood (E b))→|Real.sqrt (n b:ℝ)*c b x|≤Bc)
--       (hDa : ∀b x,x∈flipNeighborhood (E b)→‖derivativeVector (a b) x‖≤Va)
--       (hDc : ∀b x,x∈flipNeighborhood (E b)→‖derivativeVector (fun v=>Real.sqrt (n b:ℝ)*c b v) x‖≤Vc)
--       (heq : ∀b x,x∈E b→LiteralEquations (J b) j f (fld j (J b) (h b) l.val)
--         (mag j (J b) (h b) l.val) (w b) (y b) (a b) (c b) (r b) (e b) x)
--       (hdiag : ∀b x,x∈flipNeighborhood (E b)→LiteralInitialDiagnostics
--         (literalInitial (J b) j (Real.sqrt (n b:ℝ)) f (fld j (J b) (h b) l.val)
--           (mag j (J b) (h b) l.val) (a b) (c b) (r b) (e b))
--         (w b) (y b) (primaryTree j (J b) (h b) x l.val) x V S F A)
--       (Nmax : ℕ)
--       (hw : ∀b x,x∈flipNeighborhood (E b)→ClosedWordTestBound j
--         (fun i=>phi (fld j (J b) (h b) l.val x i) (r b i) (a b x)) (J b) A W (2*Nmax+5))
--       (hd : ∀b x,x∈flipNeighborhood (E b)→ClosedWordDiagramBound j
--         (fun i=>phi (fld j (J b) (h b) l.val x i) (r b i) (a b x)) (J b) A C (2*M+2*Nmax+4)) :
--       FiniteLocalRecipeControl E j J h (fun b=>literalFullParameters (M:=M) j (J b) (h b) (a b) (c b))
--         w y M Nmax A
--   ```
--
--   **Definitions.** The statement is written with `OAI.SKGap.opNorm`, `OAI.SKGapCutoff.Interaction`, `OAI.SKGapCutoff.Spin`, `OAI.SKGapCutoff.VectorFields`, `OAI.SKGap.Stein.KernelExpr`, `OAI.SKGap.Stein.phi`, `OAI.SKGapCutoff.Primary.ShapeBound`, `OAI.SKGapCutoff.Primary.derivativeVector`, `OAI.SKGapCutoff.Primary.fld`, `OAI.SKGapCutoff.Primary.formalField`, `OAI.SKGapCutoff.Primary.mag`, `OAI.SKGapCutoff.Primary.primaryTree`, `OAI.SKGapCutoff.Recipe.ClosedWordDiagramBound`, `OAI.SKGapCutoff.Recipe.ClosedWordTestBound`, `OAI.SKGapCutoff.Recipe.vectorNorm` and `OAI.SKGapCutoff.Static.flipNeighborhood` (definitions bundle `OAIQ072A000` of this split); `OAI.SKGapCutoff.Recipe.FiniteLocalRecipeControl`, `OAI.SKGapCutoff.Recipe.LiteralEquations`, `OAI.SKGapCutoff.Recipe.LiteralInitialDiagnostics`, `OAI.SKGapCutoff.Recipe.literalFullParameters` and `OAI.SKGapCutoff.Recipe.literalInitial` (definitions bundle `OAIQ072A002` of this split).
--
--   **Used by.** The proof of `OAI.SKGapCutoff.Recipe.literal_local_weak_comparison_targets` of this split imports it.
-- source:
--   OpenAI, A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/A-spectral-gap-throughout-the-high-temperature-Sherrington-Kirkpatrick-phase-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SKGap/Localization/LiteralLocalInput.lean (declaration OAI.SKGapCutoff.Recipe.literal_finite_control)

import Mathlib
import Definitions.Def_OAIQ072A002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary Static SKGap.Stein SKGap.Noncrossing.Primary SKGap.Noncrossing.Primary.Tensor.Series SKGap.Noncrossing.ClosedMarked
universe u
variable {Ω : Type u} {n : Ω→ℕ} {M : ℕ}

theorem literal_finite_control (j : ℝ) (J : ∀b,Interaction (n b))
    (h : ∀b,Fin (n b)→ℝ) (l : Fin M) (f : KernelExpr)
    (a c : ∀b,Spin (n b)→ℝ) (r e : ∀b,Fin (n b)→ℝ)
    (w y : ∀b,VectorFields (n b)) (E : ∀b,Set (Spin (n b)))
    (hn : ∀b,0<n b) (he : ∀b,vectorNorm (e b)≤1)
    {K B R Bc Va Vc A V S F W C : ℝ}
    (hK : 0≤K) (hB : 0≤B) (hBc : 0≤Bc) (hVa : 0≤Va) (hVc : 0≤Vc)
    (hA : 1≤A) (hV : 0≤V) (hS : 0≤S) (hF : 0≤F) (hW : 0≤W) (hC : 0≤C)
    (hop : ∀b,SKGap.opNorm (J b)≤K)
    (hformal : ∀b x,∀q<M,ShapeBound (formalField j (J b) (h b) x q) B)
    (ha : ∀b x,x∈flipNeighborhood (flipNeighborhood (E b))→|a b x|≤R)
    (hc : ∀b x,x∈flipNeighborhood (flipNeighborhood (E b))→|Real.sqrt (n b:ℝ)*c b x|≤Bc)
    (hDa : ∀b x,x∈flipNeighborhood (E b)→‖derivativeVector (a b) x‖≤Va)
    (hDc : ∀b x,x∈flipNeighborhood (E b)→‖derivativeVector (fun v=>Real.sqrt (n b:ℝ)*c b v) x‖≤Vc)
    (heq : ∀b x,x∈E b→LiteralEquations (J b) j f (fld j (J b) (h b) l.val)
      (mag j (J b) (h b) l.val) (w b) (y b) (a b) (c b) (r b) (e b) x)
    (hdiag : ∀b x,x∈flipNeighborhood (E b)→LiteralInitialDiagnostics
      (literalInitial (J b) j (Real.sqrt (n b:ℝ)) f (fld j (J b) (h b) l.val)
        (mag j (J b) (h b) l.val) (a b) (c b) (r b) (e b))
      (w b) (y b) (primaryTree j (J b) (h b) x l.val) x V S F A)
    (Nmax : ℕ)
    (hw : ∀b x,x∈flipNeighborhood (E b)→ClosedWordTestBound j
      (fun i=>phi (fld j (J b) (h b) l.val x i) (r b i) (a b x)) (J b) A W (2*Nmax+5))
    (hd : ∀b x,x∈flipNeighborhood (E b)→ClosedWordDiagramBound j
      (fun i=>phi (fld j (J b) (h b) l.val x i) (r b i) (a b x)) (J b) A C (2*M+2*Nmax+4)) :
    FiniteLocalRecipeControl E j J h (fun b=>literalFullParameters (M:=M) j (J b) (h b) (a b) (c b))
      w y M Nmax A := by
  sorry

end SKGapCutoff.Recipe

end
end

end OAI
end
