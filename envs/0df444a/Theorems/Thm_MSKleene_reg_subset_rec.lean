-- Prove2me | Theorems.Thm_MSKleene_reg_subset_rec
-- name    : MSKleene.reg_subset_rec
-- status  : Proved
-- author  : @Cosme
-- created : 2026-09-08T12:32:55.498129+00:00
-- url     : https://prove2.me/theorems/2c66e386-2bce-4af2-ab3e-375d37866ca7
-- title:
--   Corollary 4.8: every regular language is recognizable
-- statement:
--   **Every regular language is recognizable** (Corollary 4.8).
--
--   For every $s\in S$, $\mathrm{Reg}_{s}(\mathbf{T}_{\Sigma}(X))\subseteq\mathrm{Rec}_{s}(\mathbf{T}_{\Sigma}(X))$.
-- source:
--   Gong, Ruiz Mora, Sanmartín Vich, Cosme Llópez, "A Kleene theorem for free many-sorted algebras", 2026

import Definitions.Def_MSKleene_Recognizable
import Definitions.Def_MSKleene_Regular

namespace MSKleene

/-- **Every regular language is recognizable** (Corollary 4.8).

With `S` finite, `Σ` a finite signature, and `X` a finite `S`-sorted set:
for every sort `s`, `Reg_s(T_Σ(X)) ⊆ Rec_s(T_Σ(X))`. -/
theorem reg_subset_rec {S : Type} [Finite S] (sig : Signature S) (X : SSet S)
    (hsig : SigFinite sig) (hX : SFinite X) (s : S) :
    RegS sig X s ⊆ RecS (freeAlgebra sig X) s := by
  sorry

end MSKleene
