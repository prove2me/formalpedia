-- Prove2me | Theorems.Thm_MSKleene_iter_absorb
-- name    : MSKleene.iter_absorb
-- status  : Proved
-- author  : @Cosme
-- created : 2026-09-08T12:31:30.42246+00:00
-- url     : https://prove2.me/theorems/d6cca696-80e5-4147-8cba-6c085f94717f
-- title:
--   Lemma 3.28: iteration absorption
-- statement:
--   **Iteration absorption** (Lemma 3.28).
--
--   Let $s\in S$, $z\in X_{s}$, $L\subseteq\mathrm{T}_{\Sigma}(X)_{s}$. Then $\left(\!\begin{smallmatrix}z\\L^{\star z}\end{smallmatrix}\!\right)^{\sharp\mathsf{p}}_{s}(L)\subseteq L^{\star z}$.
-- source:
--   Gong, Ruiz Mora, Sanmartín Vich, Cosme Llópez, "A Kleene theorem for free many-sorted algebras", 2026

import Definitions.Def_MSKleene_Iteration

namespace MSKleene

/-- **Iteration absorption** (Lemma 3.28).

For `z ∈ X_s` and a language `L ⊆ T_Σ(X)_s`,
`⟨z/L^{⋆z}⟩^♯ᵖ_s(L) ⊆ L^{⋆z}`. -/
theorem iter_absorb {S : Type} (sig : Signature S) (X : SSet S) {s : S}
    (z : X s) (L : Set (Term sig X s)) :
    substP z (iterate z L) s L ⊆ iterate z L := by
  sorry

end MSKleene
