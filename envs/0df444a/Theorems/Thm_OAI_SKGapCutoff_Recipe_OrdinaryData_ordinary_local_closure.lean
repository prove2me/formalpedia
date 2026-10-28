-- Prove2me | Theorems.Thm_OAI_SKGapCutoff_Recipe_OrdinaryData_ordinary_local_closure
-- name    : OAI.SKGapCutoff.Recipe.OrdinaryData.ordinary_local_closure
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:26:32.096813+00:00
-- url     : https://prove2.me/theorems/c8ccf919-ce4c-4df1-9b1e-d612a3c6d4cf
-- title:
--   OAI.SKGapCutoff.Recipe.OrdinaryData.ordinary_local_closure: intermediate lemma from OpenAI, A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SKGap.sk_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227)*, OpenAI Math Release, September 24, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SKGapCutoff.Recipe.OrdinaryData.ordinary_local_closure` of [lean/OAI/Probability/SKGap/Stability/OrdinaryClosure.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SKGap/Stability/OrdinaryClosure.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SKGapCutoff.Recipe.OrdinaryData`, with `open scoped BigOperators Matrix.Norms.Frobenius`, `open Primary Matrix SKGap.Noncrossing SKGap.Noncrossing.Primary MarkedPolynomial`):
--
--   ```lean
--   theorem ordinary_local_closure (T : ι→SourceTree (Fin n→ℝ)) (x : Spin n) (N : ℕ)
--       (c : LocalConstants) (h : LocalOrdinaryInput D T x N c)
--       {M B Q : ℝ} (hM : 0≤M) (hB : 0≤B) (hQ : 0≤Q)
--       (hm : ∀l,mass ((T l).words D.j).1≤Q ∧ mass ((T l).words D.j).2≤Q)
--       (hw : WordTestBound D.J c.A M (2*N+3))
--       (hd : ∀a≤N,∀d:Fin n→ℝ,(∀i,|d i|≤1)→
--         (∀t∈(D.markedRecipe T x a).1,SKGap.diagonalSeminorm (matrixWord D.J (t.2.diagnostic d)-
--           Matrix.diagonal (Diagram.prediction D.j (t.2.diagnostic d)))≤B) ∧
--         (∀t∈(D.markedRecipe T x a).2,SKGap.diagonalSeminorm (matrixWord D.J (t.2.diagnostic d)-
--           Matrix.diagonal (Diagram.prediction D.j (t.2.diagnostic d)))≤B)) :
--       let W:=c.normBudget D.j (Fintype.card ι)
--       let R:=errorBudget (|D.j| *c.A) (c.sourceCost D.j (Fintype.card ι) (Fintype.card σ))
--         (c.fieldCost D.j (Fintype.card ι))
--       let V:=traceBudget ((Fintype.card ι:ℝ)*((2+|D.j|)*Q)) (2+|D.j| *c.A) W
--       ∀a≤N,SmallBound (D.source a) x (W a) ∧ SmallBound (D.auxiliary a) x (W a) ∧
--         (∑i,|derivativeMatrix (D.source a) x i i|)≤V a*B+(R a).1*M ∧
--         (∑i,|derivativeMatrix (D.auxiliary a) x i i|)≤V a*B+(R a).2*M
--   ```
--
--   **Definitions.** The statement is written with `OAI.SKGap.diagonalSeminorm`, `OAI.SKGapCutoff.Spin`, `OAI.SKGapCutoff.Primary.derivativeMatrix`, `OAI.SKGapCutoff.Recipe.OrdinaryData`, `OAI.SKGapCutoff.Recipe.SmallBound`, `OAI.SKGap.Noncrossing.Diagram.prediction`, `OAI.SKGap.Noncrossing.Primary.MarkedPolynomial`, `OAI.SKGap.Noncrossing.Primary.SmallMark`, `OAI.SKGap.Noncrossing.Primary.SourceTree`, `OAI.SKGap.Noncrossing.Primary.WordPolynomial`, `OAI.SKGap.Noncrossing.Primary.matrixWord`, `OAI.SKGap.Noncrossing.Primary.MarkedPolynomial.mass`, `OAI.SKGap.Noncrossing.Primary.SmallMark.diagnostic` and `OAI.SKGap.Noncrossing.Primary.SourceTree.words` (definitions bundle `OAIQ072A000` of this split); `OAI.SKGapCutoff.Recipe.LocalConstants`, `OAI.SKGapCutoff.Recipe.errorBudget`, `OAI.SKGapCutoff.Recipe.traceBudget`, `OAI.SKGapCutoff.Recipe.LocalConstants.fieldCost`, `OAI.SKGapCutoff.Recipe.LocalConstants.normBudget` and `OAI.SKGapCutoff.Recipe.LocalConstants.sourceCost` (definitions bundle `OAIQ072A001` of this split); `OAI.SKGapCutoff.Recipe.LocalOrdinaryInput`, `OAI.SKGapCutoff.Recipe.WordTestBound`, `OAI.SKGapCutoff.Recipe.OrdinaryData.auxiliary`, `OAI.SKGapCutoff.Recipe.OrdinaryData.markedRecipe` and `OAI.SKGapCutoff.Recipe.OrdinaryData.source` (definitions bundle `OAIQ072A002` of this split).
--
--   **Used by.** The proof of `OAI.SKGapCutoff.Recipe.primary_finite_control` of this split imports it.
-- source:
--   OpenAI, A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/A-spectral-gap-throughout-the-high-temperature-Sherrington-Kirkpatrick-phase-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SKGap/Stability/OrdinaryClosure.lean (declaration OAI.SKGapCutoff.Recipe.OrdinaryData.ordinary_local_closure)

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
open Primary Matrix SKGap.Noncrossing SKGap.Noncrossing.Primary MarkedPolynomial

variable {n : ℕ} {ι κ σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype σ]

namespace OrdinaryData
variable (D : OrdinaryData n ι κ σ)

theorem ordinary_local_closure (T : ι→SourceTree (Fin n→ℝ)) (x : Spin n) (N : ℕ)
    (c : LocalConstants) (h : LocalOrdinaryInput D T x N c)
    {M B Q : ℝ} (hM : 0≤M) (hB : 0≤B) (hQ : 0≤Q)
    (hm : ∀l,mass ((T l).words D.j).1≤Q ∧ mass ((T l).words D.j).2≤Q)
    (hw : WordTestBound D.J c.A M (2*N+3))
    (hd : ∀a≤N,∀d:Fin n→ℝ,(∀i,|d i|≤1)→
      (∀t∈(D.markedRecipe T x a).1,SKGap.diagonalSeminorm (matrixWord D.J (t.2.diagnostic d)-
        Matrix.diagonal (Diagram.prediction D.j (t.2.diagnostic d)))≤B) ∧
      (∀t∈(D.markedRecipe T x a).2,SKGap.diagonalSeminorm (matrixWord D.J (t.2.diagnostic d)-
        Matrix.diagonal (Diagram.prediction D.j (t.2.diagnostic d)))≤B)) :
    let W:=c.normBudget D.j (Fintype.card ι)
    let R:=errorBudget (|D.j| *c.A) (c.sourceCost D.j (Fintype.card ι) (Fintype.card σ))
      (c.fieldCost D.j (Fintype.card ι))
    let V:=traceBudget ((Fintype.card ι:ℝ)*((2+|D.j|)*Q)) (2+|D.j| *c.A) W
    ∀a≤N,SmallBound (D.source a) x (W a) ∧ SmallBound (D.auxiliary a) x (W a) ∧
      (∑i,|derivativeMatrix (D.source a) x i i|)≤V a*B+(R a).1*M ∧
      (∑i,|derivativeMatrix (D.auxiliary a) x i i|)≤V a*B+(R a).2*M := by
  sorry

end OrdinaryData
end SKGapCutoff.Recipe

end
end

end OAI
end
