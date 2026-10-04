-- Prove2me | Theorems.Thm_MSKleene_subst_family
-- name    : MSKleene.subst_family
-- status  : Proved
-- author  : @Cosme
-- created : 2026-09-08T12:30:59.747985+00:00
-- url     : https://prove2.me/theorems/bec30549-b673-4dc8-a818-4cdff2fe3058
-- title:
--   Lemma 3.23: substitution homomorphism as family substitution
-- statement:
--   **Substitution homomorphism as family substitution** (Lemma 3.23).
--
--   Let $u,s\in S$, $z\in X_{u}$, $L\subseteq\mathrm{T}_{\Sigma}(X)_{u}$, $P\in\mathrm{T}_{\Sigma}(X)_{s}$. Then $\left(\!\begin{smallmatrix}z\\L\end{smallmatrix}\!\right)^{\sharp}_{s}(P)=\left\{\left(\!\begin{smallmatrix}z\\(Q^{z}_{\alpha})_{\alpha\in|P|_{z}}\end{smallmatrix}\!\right)(P)\ \middle|\ (Q^{z}_{\alpha})\in L^{|P|_{z}}\right\}$. Consequently, for every $K\subseteq\mathrm{T}_{\Sigma}(X)_{s}$, $\left(\!\begin{smallmatrix}z\\L\end{smallmatrix}\!\right)^{\sharp\mathsf{p}}_{s}(K)=\bigcup_{P\in K}\left(\!\begin{smallmatrix}z\\L\end{smallmatrix}\!\right)^{\sharp}_{s}(P)$.
-- source:
--   Gong, Ruiz Mora, Sanmartín Vich, Cosme Llópez, "A Kleene theorem for free many-sorted algebras", 2026

import Definitions.Def_MSKleene_Subst
import Definitions.Def_MSKleene_SubstFam

import Definitions.Def_MSKleene_Subst
import Definitions.Def_MSKleene_SubstFam

namespace MSKleene

/-- **The substitution homomorphism as family substitution** (Lemma 3.23).

For `z ∈ X_u`, a language `L ⊆ T_Σ(X)_u`, and a term `P ∈ T_Σ(X)_s`,
`⟨z/L⟩^♯_s(P)` is the set of all `⟨z/qs⟩(P)` where `qs` ranges over families of
terms of `L` indexed by the occurrences of `z` in `P`. Consequently, its
completely additive extension on a language `K` is the union of these values
over the terms in `K`. -/
theorem subst_family {S : Type} (sig : Signature S) (X : SSet S) {u s : S}
    (z : X u) (L : Set (Term sig X u)) (P : Term sig X s) :
    ((substHom z L).toFun s P
      = { R | ∃ qs : Fin (Term.occ z P) → Term sig X u,
              (∀ α, qs α ∈ L) ∧ R = substFam z P qs })
  ∧ (∀ K : Set (Term sig X s),
      substP z L s K = ⋃ Q ∈ K, (substHom z L).toFun s Q) := by
  sorry

end MSKleene
