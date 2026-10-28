-- Prove2me | Theorems.Thm_OAI_SKGapCutoff_Recipe_OrdinaryData_implicit_started_diagonal_local
-- name    : OAI.SKGapCutoff.Recipe.OrdinaryData.implicit_started_diagonal_local
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:25:53.964397+00:00
-- url     : https://prove2.me/theorems/3692b5e1-55a3-4071-b3b3-56e77908b990
-- title:
--   OAI.SKGapCutoff.Recipe.OrdinaryData.implicit_started_diagonal_local: intermediate lemma from OpenAI, A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SKGap.sk_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227)*, OpenAI Math Release, September 24, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SKGapCutoff.Recipe.OrdinaryData.implicit_started_diagonal_local` of [lean/OAI/Probability/SKGap/Localization/LocalStartedDiagonal.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SKGap/Localization/LocalStartedDiagonal.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SKGapCutoff.Recipe.OrdinaryData`, with `open scoped BigOperators`, `open Primary Matrix SKGap SKGap.Noncrossing SKGap.Noncrossing.Primary SKGap.Noncrossing.Primary.Tensor.Series`, `open SKGap.Noncrossing.ClosedMarked`):
--
--   ```lean
--   theorem implicit_started_diagonal_local (hj : D.j=I.j) (hJ : D.J=I.J)
--       (x : Spin n)
--       (hW : w x=I.sourceOf 1 (fun _=>y) x)
--       (hWf : ∀i,w (flip x i)=I.sourceOf 1 (fun _=>y) (flip x i))
--       (hY : y x=I.fieldOf 1 (fun _=>w) (fun _=>y) x)
--       (hYf : ∀i,y (flip x i)=I.fieldOf 1 (fun _=>w) (fun _=>y) (flip x i)) (hn : 0<n)
--       (ha0 : ∀i,0≤I.implicitCoefficient x i)
--       (hS : (1-SKGap.pathDiagonal (I.implicitCoefficient x) 1*
--         (I.J-(I.j*siteMean I.implicitCoefficient x) • 1)*SKGap.pathDiagonal (I.implicitCoefficient x) 1).PosDef)
--       {C F A R M B : ℝ} {Cs Cf : ℕ→ℝ} {N : ℕ}
--       (hP : TraceControl (I.implicitSourcePrimitive t y x) C)
--       (hQ : TraceControl (I.implicitFieldPrimitive t w y x) F)
--       (hR : 0≤R) (hM : 0≤M) (hB : 0≤B) (hA : 1≤A) (ha : ∀i,|I.implicitCoefficient x i|≤A)
--       (hp : ∀a≤N,∀b i,|D.auxCoefficient a b x i|≤A)
--       (hr : ∀a≤N,∀b,|D.j*siteMean (D.auxCoefficient a b) x|≤R)
--       (hs : ∀a≤N,0<a→TraceControl (D.startedNodeSourceError w y T x a) (Cs a))
--       (hf : ∀a≤N,0<a→TraceControl (D.startedNodeFieldError w y T x a) (Cf a))
--       (hw : ClosedWordTestBound D.j (I.implicitCoefficient x) D.J A M (2*N+5))
--       (hd : ∀a≤N,∀d:Fin n→ℝ,(∀i,|d i|≤1)→∀P∈[
--           ((D.startedSmallTree w y T (.implicit (I.implicitPartial y x) t) x a).marked D.j (I.implicitCoefficient x)).1,
--           ((D.startedSmallTree w y T (.implicit (I.implicitPartial y x) t) x a).marked D.j (I.implicitCoefficient x)).2],∀v∈P,
--         diagonalSeminorm (exactWord D.j (I.implicitCoefficient x) (v.2.diagnostic d) D.J-
--           Matrix.diagonal (wordPrediction D.j (I.implicitCoefficient x) 1 (v.2.diagnostic d)))≤B) :
--       let q:=I.j*siteMean I.implicitCoefficient x
--       let Bs:=fun a=>if a=0 then C+F else Cs a
--       let Bf:=fun a=>if a=0 then |q| *(C+F)+F else Cf a
--       ∀a≤N,
--         (∑i,|derivativeMatrix (D.startedSource w y a) x i i|)≤
--           ((D.startedSmallTree w y T (.implicit (I.implicitPartial y x) t) x a).marked D.j (I.implicitCoefficient x)).1.budget*B+
--           (errorBudget R Bs Bf a).1*M ∧
--         (∑i,|derivativeMatrix (D.startedAuxiliary w y a) x i i|)≤
--           ((D.startedSmallTree w y T (.implicit (I.implicitPartial y x) t) x a).marked D.j (I.implicitCoefficient x)).2.budget*B+
--           (errorBudget R Bs Bf a).2*M
--   ```
--
--   **Definitions.** The statement is written with `OAI.SKGap.diagonalSeminorm`, `OAI.SKGap.exactWord`, `OAI.SKGap.pathDiagonal`, `OAI.SKGap.wordPrediction`, `OAI.SKGapCutoff.Interaction`, `OAI.SKGapCutoff.Spin`, `OAI.SKGapCutoff.VectorFields`, `OAI.SKGapCutoff.flip`, `OAI.SKGapCutoff.Primary.derivativeMatrix`, `OAI.SKGapCutoff.Primary.siteMean`, `OAI.SKGapCutoff.Recipe.ClosedWordTestBound`, `OAI.SKGapCutoff.Recipe.OrdinaryData`, `OAI.SKGap.Noncrossing.ClosedMarked.Mark`, `OAI.SKGap.Noncrossing.ClosedMarked.Marked`, `OAI.SKGap.Noncrossing.Primary.SourceTree`, `OAI.SKGapCutoff.Recipe.OrdinaryData.auxCoefficient`, `OAI.SKGapCutoff.Recipe.OrdinaryData.fieldOf`, `OAI.SKGapCutoff.Recipe.OrdinaryData.sourceOf`, `OAI.SKGapCutoff.Recipe.OrdinaryData.startedAuxiliary`, `OAI.SKGapCutoff.Recipe.OrdinaryData.startedSource`, `OAI.SKGap.Noncrossing.ClosedMarked.Mark.diagnostic`, `OAI.SKGap.Noncrossing.ClosedMarked.Marked.budget`, `OAI.SKGap.Noncrossing.ClosedMarked.SmallTree` and `OAI.SKGap.Noncrossing.ClosedMarked.SmallTree.marked` (definitions bundle `OAIQ072A000` of this split); `OAI.SKGapCutoff.Recipe.errorBudget` (definitions bundle `OAIQ072A001` of this split); `OAI.SKGapCutoff.Recipe.TraceControl`, `OAI.SKGapCutoff.Recipe.OrdinaryData.implicitCoefficient`, `OAI.SKGapCutoff.Recipe.OrdinaryData.implicitFieldPrimitive`, `OAI.SKGapCutoff.Recipe.OrdinaryData.implicitPartial`, `OAI.SKGapCutoff.Recipe.OrdinaryData.implicitSourcePrimitive`, `OAI.SKGapCutoff.Recipe.OrdinaryData.startedNodeFieldError`, `OAI.SKGapCutoff.Recipe.OrdinaryData.startedNodeSourceError` and `OAI.SKGapCutoff.Recipe.OrdinaryData.startedSmallTree` (definitions bundle `OAIQ072A002` of this split).
--
--   **Used by.** The proof of `OAI.SKGapCutoff.Recipe.finite_started_control_seeds` of this split imports it.
-- source:
--   OpenAI, A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/A-spectral-gap-throughout-the-high-temperature-Sherrington-Kirkpatrick-phase-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SKGap/Localization/LocalStartedDiagonal.lean (declaration OAI.SKGapCutoff.Recipe.OrdinaryData.implicit_started_diagonal_local)

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
open scoped BigOperators
namespace SKGapCutoff.Recipe.OrdinaryData
open Primary Matrix SKGap SKGap.Noncrossing SKGap.Noncrossing.Primary SKGap.Noncrossing.Primary.Tensor.Series
open SKGap.Noncrossing.ClosedMarked
variable {n : ℕ} {ι κ σ κ₀ σ₀ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype σ]
variable [Fintype κ₀] [DecidableEq κ₀] [Fintype σ₀]
variable (D : OrdinaryData n ι κ σ) (I : OrdinaryData n Unit κ₀ σ₀)
variable (w y : VectorFields n) (T : ι→SourceTree (Fin n→ℝ)) (t : SourceTree (Fin n→ℝ))

theorem implicit_started_diagonal_local (hj : D.j=I.j) (hJ : D.J=I.J)
    (x : Spin n)
    (hW : w x=I.sourceOf 1 (fun _=>y) x)
    (hWf : ∀i,w (flip x i)=I.sourceOf 1 (fun _=>y) (flip x i))
    (hY : y x=I.fieldOf 1 (fun _=>w) (fun _=>y) x)
    (hYf : ∀i,y (flip x i)=I.fieldOf 1 (fun _=>w) (fun _=>y) (flip x i)) (hn : 0<n)
    (ha0 : ∀i,0≤I.implicitCoefficient x i)
    (hS : (1-SKGap.pathDiagonal (I.implicitCoefficient x) 1*
      (I.J-(I.j*siteMean I.implicitCoefficient x) • 1)*SKGap.pathDiagonal (I.implicitCoefficient x) 1).PosDef)
    {C F A R M B : ℝ} {Cs Cf : ℕ→ℝ} {N : ℕ}
    (hP : TraceControl (I.implicitSourcePrimitive t y x) C)
    (hQ : TraceControl (I.implicitFieldPrimitive t w y x) F)
    (hR : 0≤R) (hM : 0≤M) (hB : 0≤B) (hA : 1≤A) (ha : ∀i,|I.implicitCoefficient x i|≤A)
    (hp : ∀a≤N,∀b i,|D.auxCoefficient a b x i|≤A)
    (hr : ∀a≤N,∀b,|D.j*siteMean (D.auxCoefficient a b) x|≤R)
    (hs : ∀a≤N,0<a→TraceControl (D.startedNodeSourceError w y T x a) (Cs a))
    (hf : ∀a≤N,0<a→TraceControl (D.startedNodeFieldError w y T x a) (Cf a))
    (hw : ClosedWordTestBound D.j (I.implicitCoefficient x) D.J A M (2*N+5))
    (hd : ∀a≤N,∀d:Fin n→ℝ,(∀i,|d i|≤1)→∀P∈[
        ((D.startedSmallTree w y T (.implicit (I.implicitPartial y x) t) x a).marked D.j (I.implicitCoefficient x)).1,
        ((D.startedSmallTree w y T (.implicit (I.implicitPartial y x) t) x a).marked D.j (I.implicitCoefficient x)).2],∀v∈P,
      diagonalSeminorm (exactWord D.j (I.implicitCoefficient x) (v.2.diagnostic d) D.J-
        Matrix.diagonal (wordPrediction D.j (I.implicitCoefficient x) 1 (v.2.diagnostic d)))≤B) :
    let q:=I.j*siteMean I.implicitCoefficient x
    let Bs:=fun a=>if a=0 then C+F else Cs a
    let Bf:=fun a=>if a=0 then |q| *(C+F)+F else Cf a
    ∀a≤N,
      (∑i,|derivativeMatrix (D.startedSource w y a) x i i|)≤
        ((D.startedSmallTree w y T (.implicit (I.implicitPartial y x) t) x a).marked D.j (I.implicitCoefficient x)).1.budget*B+
        (errorBudget R Bs Bf a).1*M ∧
      (∑i,|derivativeMatrix (D.startedAuxiliary w y a) x i i|)≤
        ((D.startedSmallTree w y T (.implicit (I.implicitPartial y x) t) x a).marked D.j (I.implicitCoefficient x)).2.budget*B+
        (errorBudget R Bs Bf a).2*M := by
  sorry

end SKGapCutoff.Recipe.OrdinaryData

end
end

end OAI
end
