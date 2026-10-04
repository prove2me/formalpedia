-- Prove2me | Theorems.Thm_MSKleene_rec_subset_reg
-- name    : MSKleene.rec_subset_reg
-- status  : Proved
-- author  : @Cosme
-- created : 2026-09-08T12:37:46.942064+00:00
-- url     : https://prove2.me/theorems/c0217dbd-739f-4af8-aa92-80d9f1904846
-- title:
--   Proposition 4.10: every recognizable language is regular
-- statement:
--   **Every recognizable language is regular** (Proposition 4.10).
--
--   For every $s\in S$, $\mathrm{Rec}_{s}(\mathbf{T}_{\Sigma}(X))\subseteq\mathrm{Reg}_{s}(\mathbf{T}_{\Sigma}(X))$. The proof is a constructive state elimination: from a recognizing homomorphism it builds, by induction on a sortwise budget, a regular expression denoting the language (Main Claim 4.13).
-- source:
--   Gong, Ruiz Mora, Sanmartín Vich, Cosme Llópez, "A Kleene theorem for free many-sorted algebras", 2026

import Definitions.Def_MSKleene_Recognizable
import Definitions.Def_MSKleene_Regular

namespace MSKleene

/-- **Every recognizable language is regular** (Proposition 4.10).

With `S` finite, `Σ` a finite signature, and `X` a finite `S`-sorted set:
for every sort `s`, `Rec_s(T_Σ(X)) ⊆ Reg_s(T_Σ(X))`. The proof is a
constructive state elimination carrying a sortwise budget (Main Claim 4.13). -/
theorem rec_subset_reg {S : Type} [Finite S] (sig : Signature S) (X : SSet S)
    (hsig : SigFinite sig) (hX : SFinite X) (s : S) :
    RecS (freeAlgebra sig X) s ⊆ RegS sig X s := by
  sorry

end MSKleene
