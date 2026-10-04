-- Prove2me | Theorems.Thm_MSKleene_subst_inv
-- name    : MSKleene.subst_inv
-- status  : Proved
-- author  : @Cosme
-- created : 2026-09-08T12:30:29.441813+00:00
-- url     : https://prove2.me/theorems/c11da58b-bfd5-4833-8520-e213fdd078ac
-- title:
--   Corollary 3.17: homomorphism invariance under state-preserving substitution
-- statement:
--   **Homomorphism invariance under state-preserving substitution** (Corollary 3.17).
--
--   Let $\mathbf{A}$ be a $\Sigma$-algebra and $g$ a homomorphism from $\mathbf{T}_{\Sigma}(X)$ to $\mathbf{A}$. Let $u,s\in S$, $z\in X_{u}$, $P\in\mathrm{T}_{\Sigma}(X)_{s}$, and $(Q^{z}_{\alpha})_{\alpha\in|P|_{z}}$ a family in $\mathrm{T}_{\Sigma}(X)_{u}$ with $g_{u}(Q^{z}_{\alpha})=g_{u}(z)$ for every $\alpha$. Then $g_{s}\!\left(\left(\!\begin{smallmatrix}z\\(Q^{z}_{\alpha})\end{smallmatrix}\!\right)(P)\right)=g_{s}(P)$.
-- source:
--   Gong, Ruiz Mora, Sanmartín Vich, Cosme Llópez, "A Kleene theorem for free many-sorted algebras", 2026

import Definitions.Def_MSKleene_SubstFam

namespace MSKleene

/-- **Homomorphism invariance under state-preserving substitution**
(Corollary 3.17).

If `g : T_Σ(X) → A` is a homomorphism, `z ∈ X_u`, `P ∈ T_Σ(X)_s`, and the family
`qs` substituted for the occurrences of `z` in `P` satisfies `g_u(qs α) = g_u(z)`
for every `α`, then `g_s(⟨z/qs⟩(P)) = g_s(P)`. -/
theorem subst_inv {S : Type} (sig : Signature S) (X : SSet S) (A : Algebra sig)
    (g : Hom (freeAlgebra sig X) A) {u s : S} (z : X u) (P : Term sig X s)
    (qs : Fin (Term.occ z P) → Term sig X u)
    (hq : ∀ α, g.toFun u (qs α) = g.toFun u (Term.var z)) :
    g.toFun s (substFam z P qs) = g.toFun s P := by
  sorry

end MSKleene
