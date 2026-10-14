-- Prove2me | Theorems.Thm_MoritaEquiv_Sig_Hom_IsRenaming_exists_formula_pullback
-- name    : MoritaEquiv.Sig.Hom.IsRenaming.exists_formula_pullback
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-13T20:02:41.623613+00:00
-- url     : https://prove2.me/theorems/a4c654c8-1667-4eb3-af2c-78dc44f0137d
-- title:
--   Formulas pull back along a renaming of signatures
-- statement:
--   Let $F:\Sigma\to\Sigma'$ be a renaming of many-sorted signatures, i.e. a signature morphism that is bijective on sorts and, for each arity, bijective on function and relation symbols. Let $\Gamma$ be a $\Sigma$-context.
--
--   **Statement.** Every $\Sigma'$-formula $\varphi$ in the context $F(\Gamma)$ is equivalent to the $F$-translation of some $\Sigma$-formula $\psi$ in context $\Gamma$. That is, for every $\Sigma'$-structure $M$ and every assignment $v$, $M\models\varphi[v] \iff M\models F(\psi)[v]$.
--
--   The proof is by induction on terms and formulas, pulling back each sort and symbol along the inverse of $F$. Together with translation along $F$ this shows that a renaming identifies the two languages, which is needed whenever Morita equivalence is defined up to renaming of the common signature.
--
--   **Formalization Note** The context of $\varphi$ is written `F.onSrt ∘ Γ`; the equivalence is stated for all structures (no theory).
-- source:
--   T. W. Barrett, H. Halvorson, Morita Equivalence, Rev. Symb. Logic 9 (2016) 556-582, https://arxiv.org/abs/1506.04675, §4-§5 (used for the second half of Theorem 5.2)

import Mathlib
import Definitions.Def_MoritaEquiv_defs

open CategoryTheory

namespace MoritaEquiv

/-- Formulas can be pulled back along a renaming: if `F : L ⟶ L'` is a renaming (bijective on
sorts and on the symbols of each arity), every `L'`-formula whose context is the `F`-image of an
`L`-context `Γ` is equivalent, in every `L'`-structure, to the `F`-translation of an `L`-formula
in context `Γ`. -/
theorem Sig.Hom.IsRenaming.exists_formula_pullback {L L' : Sig} {F : L.Hom L'} (hF : F.IsRenaming)
    {n : ℕ} (Γ : Fin n → L.Srt) (φ : Formula L' (F.onSrt ∘ Γ)) :
    ∃ ψ : Formula L Γ, ∀ (M : Str L') (v : (i : Fin n) → M.carrier (F.onSrt (Γ i))),
      φ.Realize M v ↔ (ψ.onFormula F).Realize M v := by sorry

end MoritaEquiv
