-- Prove2me | Theorems.Thm_MoritaEquiv_conservative
-- name    : MoritaEquiv.conservative
-- status  : Open
-- author  : @Alien60
-- created : 2026-10-10T12:58:54.934617+00:00
-- url     : https://prove2.me/theorems/477e96ff-7e9b-4c01-ab4b-859dc268c078
-- title:
--   Morita extensions are conservative
-- statement:
--   Throughout: many-sorted first-order logic with nonempty sorts; $\mathrm{Mod}(T)$ has the models of $T$ as objects and elementary embeddings as arrows; $D$ is a Morita extension of the $\Sigma$-theory $T$ (new product, coproduct, subsort and quotient sorts and explicitly defined symbols, with admissibility in every model of $T$), $T^+$ the extended theory and $\Pi:\mathrm{Mod}(T^+)\to\mathrm{Mod}(T)$ the reduct functor. For every $\Sigma$-formula $\alpha$ in context: $\alpha$ holds in all models of $T$ iff (its image) holds in all models of $T^+$.
-- source:
--   T. W. Barrett, H. Halvorson, Morita Equivalence, Rev. Symb. Logic 9 (2016) 556-582, https://arxiv.org/abs/1506.04675 (numbering as in arXiv v1), §4.2, Theorem 4.2

import Mathlib
import Definitions.Def_MoritaEquiv_defs

open CategoryTheory

namespace MoritaEquiv

/-- Barrett–Halvorson, Theorem 4.2: a Morita extension `T⁺` of `T` is conservative:
`T ⊨ A` iff `T⁺ ⊨ A` for every `Σ`-axiom `A` (formula in context, read as its universal closure). -/
theorem conservative {L : Sig} {T : Theory L} (D : MoritaData L T) (A : Axiom L) :
    (∀ M : Model T, M.str.Satisfies A) ↔ ∀ N : Model D.ext, N.str.Satisfies (A.map D.incl) := by sorry

end MoritaEquiv
