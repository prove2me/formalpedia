-- Prove2me | Theorems.Thm_MoritaEquiv_MoritaData_exists_isolated_model_iff
-- name    : MoritaEquiv.MoritaData.exists_isolated_model_iff
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-13T20:02:43.930861+00:00
-- url     : https://prove2.me/theorems/e612e9d4-9c2b-40c8-918d-6e916ceeebbd
-- title:
--   Morita extensions preserve sentence-isolated models
-- statement:
--   Let $T^+$ (over $\Sigma^+$) be a Morita extension of the $\Sigma$-theory $T$. Say a theory has an **isolated model** if there are a model $M$ and a sentence $\varphi$ with $M\models\varphi$ such that every model $N\models\varphi$ of the theory admits an elementary embedding $N\to M$.
--
--   **Statement.** $T$ has an isolated model if and only if $T^+$ has an isolated model.
--
--   ($\Rightarrow$) Take the expansion of $M$ to a model of $T^+$ and the same sentence read in $\Sigma^+$. Elementary embeddings between reducts lift because the reduct functor is full. ($\Leftarrow$) Translate the $\Sigma^+$-sentence into a $T^+$-equivalent $\Sigma$-sentence, and use that every model of $T$ expands to a model of $T^+$. So the property is an invariant of Morita equivalence. Barrett–Halvorson's Theorem 5.2 uses it to separate Morita equivalence from categorical equivalence.
--
--   **Formalization Note** Sentences are formulas in an empty context `Γ : Fin 0 → Srt`. Arrows `N ⟶ M` are morphisms of the category of models, i.e. elementary embeddings.
-- source:
--   T. W. Barrett, H. Halvorson, Morita Equivalence, Rev. Symb. Logic 9 (2016) 556-582, https://arxiv.org/abs/1506.04675, §4-§5 (used for the second half of Theorem 5.2)

import Mathlib
import Definitions.Def_MoritaEquiv_defs

open CategoryTheory

namespace MoritaEquiv

/-- Morita extensions preserve the existence of a sentence-isolated model: `T` has a model `M` and a
sentence `φ` true in `M` such that every model of `T` satisfying `φ` elementarily embeds into `M`
if and only if the Morita extension `T⁺` has such a model and sentence. -/
theorem MoritaData.exists_isolated_model_iff {L : Sig} {T : Theory L} (D : MoritaData L T) :
    (∃ (M : Model T) (Γ : Fin 0 → L.Srt) (φ : Formula L Γ), (∀ v, φ.Realize M.str v) ∧
      ∀ N : Model T, (∀ v, φ.Realize N.str v) → Nonempty (N ⟶ M)) ↔
    (∃ (M : Model D.ext) (Γ : Fin 0 → D.sig.Srt) (φ : Formula D.sig Γ), (∀ v, φ.Realize M.str v) ∧
      ∀ N : Model D.ext, (∀ v, φ.Realize N.str v) → Nonempty (N ⟶ M)) := by sorry

end MoritaEquiv
