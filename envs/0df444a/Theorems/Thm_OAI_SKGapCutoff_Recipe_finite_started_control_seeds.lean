-- Prove2me | Theorems.Thm_OAI_SKGapCutoff_Recipe_finite_started_control_seeds
-- name    : OAI.SKGapCutoff.Recipe.finite_started_control_seeds
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:27:13.889864+00:00
-- url     : https://prove2.me/theorems/299ba213-4914-4c11-8b96-df7aad6f08d4
-- title:
--   OAI.SKGapCutoff.Recipe.finite_started_control_seeds: intermediate lemma from OpenAI, A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SKGap.sk_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227)*, OpenAI Math Release, September 24, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SKGapCutoff.Recipe.finite_started_control_seeds` of [lean/OAI/Probability/SKGap/Localization/FiniteStartedControlGeneral.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SKGap/Localization/FiniteStartedControlGeneral.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SKGapCutoff.Recipe`, with `open scoped BigOperators Matrix.Norms.Frobenius`, `open Primary Static Matrix SKGap SKGap.Noncrossing SKGap.Noncrossing.Primary SKGap.Noncrossing.Primary.Tensor.Series SKGap.Noncrossing.ClosedMarked`):
--
--   ```lean
--   theorem finite_started_control_seeds (D₀ : ∀a,OrdinaryData (n a) (Fin M) κ σ₁)
--       (K₀ : ℝ) (H₀ : LocalFamilyRecipe E j J h Θ w y D₀ 1 0 K₀)
--       (I : ∀a,OrdinaryData (n a) Unit κ₀ σ₀)
--       (hij : ∀a,(I a).j=j) (hIJ : ∀a,(I a).J=J a)
--       (T : ∀a,Spin (n a)→Fin M→SourceTree (Fin (n a)→ℝ))
--       (t : ∀a,Spin (n a)→SourceTree (Fin (n a)→ℝ))
--       (c : LocalConstants) (A : ℝ)
--       (hc : ∀a x,x∈flipNeighborhood (E a)→LocalOrdinaryInput (D₀ a) (T a x) x 1 c)
--       (index : Fin M→κ)
--       (hθ : ∀a q,(D₀ a).θ (index q)=fun x=>j*(onsager j (J a) (h a) (q.val+1) x-onsager j (J a) (h a) q.val x))
--       (Nmax L : ℕ) (C F B₀ W B Q : ℝ) (hA : 1≤A)
--       (hC : 0≤C) (hF : 0≤F) (hB₀ : 0≤B₀) (hW : 0≤W) (hB : 0≤B) (hQ : 0≤Q)
--       (hW₀ : ∀a x,x∈flipNeighborhood (E a)→w a x=(I a).sourceOf 1 (fun _=>y a) x)
--       (hWf : ∀a x,x∈flipNeighborhood (E a)→∀i,w a (flip x i)=(I a).sourceOf 1 (fun _=>y a) (flip x i))
--       (hY₀ : ∀a x,x∈flipNeighborhood (E a)→y a x=(I a).fieldOf 1 (fun _=>w a) (fun _=>y a) x)
--       (hYf : ∀a x,x∈flipNeighborhood (E a)→∀i,y a (flip x i)=(I a).fieldOf 1 (fun _=>w a) (fun _=>y a) (flip x i))
--       (ha0 : ∀a x,x∈flipNeighborhood (E a)→∀i,0≤(I a).implicitCoefficient x i)
--       (hS : ∀a x,x∈flipNeighborhood (E a)→(1-SKGap.pathDiagonal ((I a).implicitCoefficient x) 1*
--         ((I a).J-((I a).j*siteMean (I a).implicitCoefficient x) • 1)*SKGap.pathDiagonal ((I a).implicitCoefficient x) 1).PosDef)
--       (hw₀ : ∀a x,x∈flipNeighborhood (E a)→SmallBound (w a) x B₀)
--       (hy₀ : ∀a x,x∈flipNeighborhood (E a)→SmallBound (y a) x B₀)
--       (hp₀ : ∀a x,x∈flipNeighborhood (E a)→vectorNorm ((I a).implicitPartial (y a) x)≤B₀)
--       (hP : ∀a x,x∈flipNeighborhood (E a)→TraceControl ((I a).implicitSourcePrimitive (t a x) (y a) x) C)
--       (hF' : ∀a x,x∈flipNeighborhood (E a)→TraceControl ((I a).implicitFieldPrimitive (t a x) (w a) (y a) x) F)
--       (ha : ∀a x,x∈flipNeighborhood (E a)→∀i,|(I a).implicitCoefficient x i|≤A)
--       (hm : ∀a x,x∈flipNeighborhood (E a)→∀l,Marked.mass (GradedWords.ordinaryWords j (T a x l)).1≤Q ∧ Marked.mass (GradedWords.ordinaryWords j (T a x l)).2≤Q)
--       (hm₀ : ∀a x,x∈flipNeighborhood (E a)→Marked.mass (GradedWords.ordinaryWords j (t a x)).1≤Q ∧ Marked.mass (GradedWords.ordinaryWords j (t a x)).2≤Q)
--       (hT : ∀a x,x∈flipNeighborhood (E a)→∀l,GradedControl A L (GradedWords.ordinaryWords j (T a x l)).1 ∧ GradedControl A L (GradedWords.ordinaryWords j (T a x l)).2)
--       (ht : ∀a x,x∈flipNeighborhood (E a)→GradedControl A L (GradedWords.ordinaryWords j (t a x)).1 ∧ GradedControl A L (GradedWords.ordinaryWords j (t a x)).2)
--       (hw : ∀a x,x∈flipNeighborhood (E a)→ClosedWordTestBound j ((I a).implicitCoefficient x) (J a) A W (2*Nmax+5))
--       (hd : ∀a x,x∈flipNeighborhood (E a)→ClosedWordDiagramBound j ((I a).implicitCoefficient x) (J a) A B (L+2*Nmax+3)) :
--       FiniteLocalRecipeControl E j J h Θ w y M Nmax A
--   ```
--
--   **Definitions.** The statement is written with `OAI.SKGap.pathDiagonal`, `OAI.SKGapCutoff.Interaction`, `OAI.SKGapCutoff.Observables`, `OAI.SKGapCutoff.Spin`, `OAI.SKGapCutoff.VectorFields`, `OAI.SKGapCutoff.flip`, `OAI.SKGapCutoff.Primary.onsager`, `OAI.SKGapCutoff.Primary.siteMean`, `OAI.SKGapCutoff.Recipe.ClosedWordDiagramBound`, `OAI.SKGapCutoff.Recipe.ClosedWordTestBound`, `OAI.SKGapCutoff.Recipe.LocalFamilyRecipe`, `OAI.SKGapCutoff.Recipe.OrdinaryData`, `OAI.SKGapCutoff.Recipe.SmallBound`, `OAI.SKGapCutoff.Recipe.vectorNorm`, `OAI.SKGapCutoff.Static.flipNeighborhood`, `OAI.SKGap.Noncrossing.ClosedMarked.GradedControl`, `OAI.SKGap.Noncrossing.Primary.SourceTree`, `OAI.SKGapCutoff.Recipe.OrdinaryData.fieldOf`, `OAI.SKGapCutoff.Recipe.OrdinaryData.sourceOf`, `OAI.SKGap.Noncrossing.ClosedMarked.Marked.mass`, `OAI.SKGap.Noncrossing.Primary.Tensor.Series.GradedWords` and `OAI.SKGap.Noncrossing.Primary.Tensor.Series.GradedWords.ordinaryWords` (definitions bundle `OAIQ072A000` of this split); `OAI.SKGapCutoff.Recipe.LocalConstants` (definitions bundle `OAIQ072A001` of this split); `OAI.SKGapCutoff.Recipe.FiniteLocalRecipeControl`, `OAI.SKGapCutoff.Recipe.LocalOrdinaryInput`, `OAI.SKGapCutoff.Recipe.TraceControl`, `OAI.SKGapCutoff.Recipe.OrdinaryData.implicitCoefficient`, `OAI.SKGapCutoff.Recipe.OrdinaryData.implicitFieldPrimitive`, `OAI.SKGapCutoff.Recipe.OrdinaryData.implicitPartial` and `OAI.SKGapCutoff.Recipe.OrdinaryData.implicitSourcePrimitive` (definitions bundle `OAIQ072A002` of this split).
--
--   **Used by.** The proof of `OAI.SKGapCutoff.Recipe.literal_finite_control` of this split imports it.
-- source:
--   OpenAI, A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/A-spectral-gap-throughout-the-high-temperature-Sherrington-Kirkpatrick-phase-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SKGap/Localization/FiniteStartedControlGeneral.lean (declaration OAI.SKGapCutoff.Recipe.finite_started_control_seeds)

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
open Primary Static Matrix SKGap SKGap.Noncrossing SKGap.Noncrossing.Primary SKGap.Noncrossing.Primary.Tensor.Series SKGap.Noncrossing.ClosedMarked
universe u
variable {σ₁ : Type} [Fintype σ₁]
variable {Ω : Type u} {n : Ω→ℕ} {κ κ₀ σ₀ : Type} [Fintype κ] [DecidableEq κ] [Fintype κ₀] [DecidableEq κ₀] [Fintype σ₀]
variable {M : ℕ} {j : ℝ} {J : ∀a,Interaction (n a)} {h : ∀a,Fin (n a)→ℝ}
variable {E : ∀a,Set (Spin (n a))} {Θ : ∀a,κ→Observables (n a)} {w y : ∀a,VectorFields (n a)}

theorem finite_started_control_seeds (D₀ : ∀a,OrdinaryData (n a) (Fin M) κ σ₁)
    (K₀ : ℝ) (H₀ : LocalFamilyRecipe E j J h Θ w y D₀ 1 0 K₀)
    (I : ∀a,OrdinaryData (n a) Unit κ₀ σ₀)
    (hij : ∀a,(I a).j=j) (hIJ : ∀a,(I a).J=J a)
    (T : ∀a,Spin (n a)→Fin M→SourceTree (Fin (n a)→ℝ))
    (t : ∀a,Spin (n a)→SourceTree (Fin (n a)→ℝ))
    (c : LocalConstants) (A : ℝ)
    (hc : ∀a x,x∈flipNeighborhood (E a)→LocalOrdinaryInput (D₀ a) (T a x) x 1 c)
    (index : Fin M→κ)
    (hθ : ∀a q,(D₀ a).θ (index q)=fun x=>j*(onsager j (J a) (h a) (q.val+1) x-onsager j (J a) (h a) q.val x))
    (Nmax L : ℕ) (C F B₀ W B Q : ℝ) (hA : 1≤A)
    (hC : 0≤C) (hF : 0≤F) (hB₀ : 0≤B₀) (hW : 0≤W) (hB : 0≤B) (hQ : 0≤Q)
    (hW₀ : ∀a x,x∈flipNeighborhood (E a)→w a x=(I a).sourceOf 1 (fun _=>y a) x)
    (hWf : ∀a x,x∈flipNeighborhood (E a)→∀i,w a (flip x i)=(I a).sourceOf 1 (fun _=>y a) (flip x i))
    (hY₀ : ∀a x,x∈flipNeighborhood (E a)→y a x=(I a).fieldOf 1 (fun _=>w a) (fun _=>y a) x)
    (hYf : ∀a x,x∈flipNeighborhood (E a)→∀i,y a (flip x i)=(I a).fieldOf 1 (fun _=>w a) (fun _=>y a) (flip x i))
    (ha0 : ∀a x,x∈flipNeighborhood (E a)→∀i,0≤(I a).implicitCoefficient x i)
    (hS : ∀a x,x∈flipNeighborhood (E a)→(1-SKGap.pathDiagonal ((I a).implicitCoefficient x) 1*
      ((I a).J-((I a).j*siteMean (I a).implicitCoefficient x) • 1)*SKGap.pathDiagonal ((I a).implicitCoefficient x) 1).PosDef)
    (hw₀ : ∀a x,x∈flipNeighborhood (E a)→SmallBound (w a) x B₀)
    (hy₀ : ∀a x,x∈flipNeighborhood (E a)→SmallBound (y a) x B₀)
    (hp₀ : ∀a x,x∈flipNeighborhood (E a)→vectorNorm ((I a).implicitPartial (y a) x)≤B₀)
    (hP : ∀a x,x∈flipNeighborhood (E a)→TraceControl ((I a).implicitSourcePrimitive (t a x) (y a) x) C)
    (hF' : ∀a x,x∈flipNeighborhood (E a)→TraceControl ((I a).implicitFieldPrimitive (t a x) (w a) (y a) x) F)
    (ha : ∀a x,x∈flipNeighborhood (E a)→∀i,|(I a).implicitCoefficient x i|≤A)
    (hm : ∀a x,x∈flipNeighborhood (E a)→∀l,Marked.mass (GradedWords.ordinaryWords j (T a x l)).1≤Q ∧ Marked.mass (GradedWords.ordinaryWords j (T a x l)).2≤Q)
    (hm₀ : ∀a x,x∈flipNeighborhood (E a)→Marked.mass (GradedWords.ordinaryWords j (t a x)).1≤Q ∧ Marked.mass (GradedWords.ordinaryWords j (t a x)).2≤Q)
    (hT : ∀a x,x∈flipNeighborhood (E a)→∀l,GradedControl A L (GradedWords.ordinaryWords j (T a x l)).1 ∧ GradedControl A L (GradedWords.ordinaryWords j (T a x l)).2)
    (ht : ∀a x,x∈flipNeighborhood (E a)→GradedControl A L (GradedWords.ordinaryWords j (t a x)).1 ∧ GradedControl A L (GradedWords.ordinaryWords j (t a x)).2)
    (hw : ∀a x,x∈flipNeighborhood (E a)→ClosedWordTestBound j ((I a).implicitCoefficient x) (J a) A W (2*Nmax+5))
    (hd : ∀a x,x∈flipNeighborhood (E a)→ClosedWordDiagramBound j ((I a).implicitCoefficient x) (J a) A B (L+2*Nmax+3)) :
    FiniteLocalRecipeControl E j J h Θ w y M Nmax A := by
  sorry

end SKGapCutoff.Recipe

end
end

end OAI
end
