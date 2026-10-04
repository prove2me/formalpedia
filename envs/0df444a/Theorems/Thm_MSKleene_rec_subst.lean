-- Prove2me | Theorems.Thm_MSKleene_rec_subst
-- name    : MSKleene.rec_subst
-- status  : Proved
-- author  : @Cosme
-- created : 2026-09-08T12:31:54.078456+00:00
-- url     : https://prove2.me/theorems/7e83e436-eddb-4236-ae6f-6c3f128a288b
-- title:
--   Proposition 3.30: recognizability closed under substitution
-- statement:
--   **Recognizability closed under substitution** (Proposition 3.30).
--
--   Assume $S$ and $X$ finite. Let $s\in S$, $K\in\mathrm{Rec}_{s}(\mathbf{T}_{\Sigma}(X))$, and $\left((\!\begin{smallmatrix}x\\L_{x}\end{smallmatrix}\!)_{x\in X_{t}}\right)_{t\in S}$ an $S$-sorted mapping from $X$ into $(\mathrm{Rec}_{t}(\mathbf{T}_{\Sigma}(X)))_{t}$. Then $\left(\left((\!\begin{smallmatrix}x\\L_{x}\end{smallmatrix}\!)_{x\in X_{t}}\right)_{t\in S}\right)^{\sharp\mathsf{p}}_{s}(K)\in\mathrm{Rec}_{s}(\mathbf{T}_{\Sigma}(X))$. (From CVCL20, Prop. 3.19.)
-- source:
--   Gong, Ruiz Mora, Sanmartín Vich, Cosme Llópez, "A Kleene theorem for free many-sorted algebras", 2026

import Definitions.Def_MSKleene_Recognizable
import Definitions.Def_MSKleene_SubstGlobal

namespace MSKleene

/-- **Recognizability is closed under substitution** (Proposition 3.30; from CVCL20).

With `S` and `X` finite: if `K ⊆ T_Σ(X)_s` is `s`-recognizable and
`ρ` assigns to every variable a recognizable language, then the global
substitution `ρ^♯ᵖ_s(K)` is `s`-recognizable. -/
theorem rec_subst {S : Type} [Finite S] (sig : Signature S) (X : SSet S)
    (hX : SFinite X) {s : S} (K : Set (Term sig X s))
    (hK : sRecognizable (freeAlgebra sig X) s K)
    (ρ : SMap X (powerAlgebra (freeAlgebra sig X)).carrier)
    (hρ : ∀ (t : S) (x : X t), sRecognizable (freeAlgebra sig X) t (ρ t x)) :
    sRecognizable (freeAlgebra sig X) s (substGlobalP ρ s K) := by
  sorry

end MSKleene
