-- Prove2me | Theorems.Thm_MSKleene_rec_op
-- name    : MSKleene.rec_op
-- status  : Proved
-- author  : @Cosme
-- created : 2026-09-08T12:32:16.315839+00:00
-- url     : https://prove2.me/theorems/0315b33f-0b4b-4cd0-b0d7-e52de2d16298
-- title:
--   Corollary 3.32: operation symbols preserve recognizability
-- statement:
--   **Operation symbols preserve recognizability** (Corollary 3.32).
--
--   Let $(\mathbf{s},s)\in S^{\star}\times S$, $\sigma\in\Sigma_{\mathbf{s},s}$, and $(L_{j})_{j}\in\prod_{j}\mathrm{Rec}_{s_{j}}(\mathbf{T}_{\Sigma}(X))$. Then $\sigma^{\mathbf{T}_{\Sigma}(X)^{\wp}}((L_{j})_{j})\in\mathrm{Rec}_{s}(\mathbf{T}_{\Sigma}(X))$. (From CVCL20, Cor. 3.21.)
-- source:
--   Gong, Ruiz Mora, Sanmartín Vich, Cosme Llópez, "A Kleene theorem for free many-sorted algebras", 2026

import Definitions.Def_MSKleene_Term
import Definitions.Def_MSKleene_Recognizable
import Definitions.Def_MSKleene_Power

namespace MSKleene

/-- **Operation symbols preserve recognizability** (Corollary 3.32; from CVCL20).

With `S` and `X` finite: for `σ ∈ Σ_{w,s}` and a tuple `Ls` of languages, each
`s_j`-recognizable, the image `σ^{T_Σ(X)^℘}(Ls)` is `s`-recognizable. -/
theorem rec_op {S : Type} [Finite S] (sig : Signature S) (X : SSet S)
    (hX : SFinite X) {w : List S} {s : S} (σ : sig w s)
    (Ls : Args (fun s => Set (Term sig X s)) w)
    (hLs : Args.All (fun s L => sRecognizable (freeAlgebra sig X) s L) Ls) :
    sRecognizable (freeAlgebra sig X) s (powerOp (freeAlgebra sig X) σ Ls) := by
  sorry

end MSKleene
