-- Prove2me | Theorems.Thm_MSKleene_rec_subst_single
-- name    : MSKleene.rec_subst_single
-- status  : Proved
-- author  : @Cosme
-- created : 2026-09-08T12:32:05.235223+00:00
-- url     : https://prove2.me/theorems/f1a2eaa7-4851-4a0e-92a6-6a70896e25fc
-- title:
--   Corollary 3.31: single-variable substitution preserves recognizability
-- statement:
--   **Single-variable substitution preserves recognizability** (Corollary 3.31).
--
--   Assume $S$ and $X$ finite. Let $s,t\in S$, $z\in X_{t}$, $L\in\mathrm{Rec}_{t}(\mathbf{T}_{\Sigma}(X))$, and $K\in\mathrm{Rec}_{s}(\mathbf{T}_{\Sigma}(X))$. Then $\left(\!\begin{smallmatrix}z\\L\end{smallmatrix}\!\right)^{\sharp\mathsf{p}}_{s}(K)\in\mathrm{Rec}_{s}(\mathbf{T}_{\Sigma}(X))$. (From CVCL20, Cor. 3.20.)
-- source:
--   Gong, Ruiz Mora, Sanmartín Vich, Cosme Llópez, "A Kleene theorem for free many-sorted algebras", 2026

import Definitions.Def_MSKleene_Recognizable
import Definitions.Def_MSKleene_Subst

namespace MSKleene

/-- **Single-variable substitution preserves recognizability** (Corollary 3.31;
from CVCL20).

With `S` and `X` finite: for `z ∈ X_t`, if `L ⊆ T_Σ(X)_t` and `K ⊆ T_Σ(X)_s`
are recognizable, then `⟨z/L⟩^♯ᵖ_s(K)` is `s`-recognizable. -/
theorem rec_subst_single {S : Type} [Finite S] (sig : Signature S) (X : SSet S)
    (hX : SFinite X) {s t : S} (z : X t) (L : Set (Term sig X t))
    (K : Set (Term sig X s)) (hL : sRecognizable (freeAlgebra sig X) t L)
    (hK : sRecognizable (freeAlgebra sig X) s K) :
    sRecognizable (freeAlgebra sig X) s (substP z L s K) := by
  sorry

end MSKleene
