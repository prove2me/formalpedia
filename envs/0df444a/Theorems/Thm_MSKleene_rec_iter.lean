-- Prove2me | Theorems.Thm_MSKleene_rec_iter
-- name    : MSKleene.rec_iter
-- status  : Proved
-- author  : @Cosme
-- created : 2026-09-08T12:32:29.251655+00:00
-- url     : https://prove2.me/theorems/3eb28bde-f2c5-4e95-8d5c-c95764c00993
-- title:
--   Proposition 3.33: recognizability closed under iteration
-- statement:
--   **Recognizability closed under iteration** (Proposition 3.33).
--
--   Assume $S$ finite. Let $s\in S$ and $z\in X_{s}$. If $L\in\mathrm{Rec}_{s}(\mathbf{T}_{\Sigma}(X))$ then $L^{\star z}\in\mathrm{Rec}_{s}(\mathbf{T}_{\Sigma}(X))$. (From CVCL20, Prop. 3.25.)
-- source:
--   Gong, Ruiz Mora, Sanmartín Vich, Cosme Llópez, "A Kleene theorem for free many-sorted algebras", 2026

import Definitions.Def_MSKleene_Recognizable
import Definitions.Def_MSKleene_Iteration

namespace MSKleene

/-- **Iteration preserves recognizability** (Proposition 3.33; from CVCL20).

With `S` finite: for `z ∈ X_s`, if `L ⊆ T_Σ(X)_s` is `s`-recognizable then so is
its `z`-iteration `L^{⋆z}`. -/
theorem rec_iter {S : Type} [Finite S] (sig : Signature S) (X : SSet S) {s : S}
    (z : X s) (L : Set (Term sig X s)) (hL : sRecognizable (freeAlgebra sig X) s L) :
    sRecognizable (freeAlgebra sig X) s (iterate z L) := by
  sorry

end MSKleene
