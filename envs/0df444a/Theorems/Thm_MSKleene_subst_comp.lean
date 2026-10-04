-- Prove2me | Theorems.Thm_MSKleene_subst_comp
-- name    : MSKleene.subst_comp
-- status  : Proved
-- author  : @Cosme
-- created : 2026-09-08T12:31:16.338431+00:00
-- url     : https://prove2.me/theorems/1f427aa8-68d4-4f42-add8-19ef43c45351
-- title:
--   Lemma 3.25: substitution composition inclusion
-- statement:
--   **Substitution composition inclusion** (Lemma 3.25).
--
--   Let $u,s\in S$, $z\in X_{u}$, $L,L'\subseteq\mathrm{T}_{\Sigma}(X)_{u}$, and $K\subseteq\mathrm{T}_{\Sigma}(X)_{s}$. Then $\left(\!\begin{smallmatrix}z\\\left(\!\begin{smallmatrix}z\\L\end{smallmatrix}\!\right)^{\sharp\mathsf{p}}_{u}(L')\end{smallmatrix}\!\right)^{\sharp\mathsf{p}}_{s}(K)\subseteq\left(\!\begin{smallmatrix}z\\L\end{smallmatrix}\!\right)^{\sharp\mathsf{p}}_{s}\!\left(\left(\!\begin{smallmatrix}z\\L'\end{smallmatrix}\!\right)^{\sharp\mathsf{p}}_{s}(K)\right)$.
-- source:
--   Gong, Ruiz Mora, Sanmartín Vich, Cosme Llópez, "A Kleene theorem for free many-sorted algebras", 2026

import Definitions.Def_MSKleene_Subst

namespace MSKleene

/-- **Substitution composition inclusion** (Lemma 3.25).

For `z ∈ X_u`, languages `L, L' ⊆ T_Σ(X)_u`, and `K ⊆ T_Σ(X)_s`,
`⟨z/⟨z/L⟩^♯ᵖ_u(L')⟩^♯ᵖ_s(K) ⊆ ⟨z/L⟩^♯ᵖ_s(⟨z/L'⟩^♯ᵖ_s(K))`. -/
theorem subst_comp {S : Type} (sig : Signature S) (X : SSet S) {u s : S}
    (z : X u) (L L' : Set (Term sig X u)) (K : Set (Term sig X s)) :
    substP z (substP z L u L') s K ⊆ substP z L s (substP z L' s K) := by
  sorry

end MSKleene
