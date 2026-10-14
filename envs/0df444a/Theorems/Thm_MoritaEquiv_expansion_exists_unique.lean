-- Prove2me | Theorems.Thm_MoritaEquiv_expansion_exists_unique
-- name    : MoritaEquiv.expansion_exists_unique
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-10T12:57:15.945081+00:00
-- url     : https://prove2.me/theorems/7dfb9b4e-9ba9-4bde-bbec-7a726fc09a8d
-- title:
--   Every model of T expands uniquely to a model of T⁺
-- statement:
--   Throughout: many-sorted first-order logic with nonempty sorts; $\mathrm{Mod}(T)$ has the models of $T$ as objects and elementary embeddings as arrows; $D$ is a Morita extension of the $\Sigma$-theory $T$ (new product, coproduct, subsort and quotient sorts and explicitly defined symbols, with admissibility in every model of $T$), $T^+$ the extended theory and $\Pi:\mathrm{Mod}(T^+)\to\mathrm{Mod}(T)$ the reduct functor. For every $M\in\mathrm{Mod}(T)$ there is $N\in\mathrm{Mod}(T^+)$ with $\Pi N\cong M$, and any two $N,N'$ with $\Pi N\cong M\cong\Pi N'$ are isomorphic in $\mathrm{Mod}(T^+)$.
-- source:
--   T. W. Barrett, H. Halvorson, Morita Equivalence, Rev. Symb. Logic 9 (2016) 556-582, https://arxiv.org/abs/1506.04675 (numbering as in arXiv v1), §4.2, Theorem 4.1 (with Prop. 5.1)

import Mathlib
import Definitions.Def_MoritaEquiv_defs

open CategoryTheory

namespace MoritaEquiv

/-- Barrett–Halvorson, Theorem 4.1 (with Proposition 5.1): if `T⁺` is a Morita extension of `T`,
every model `M` of `T` has an expansion that is a model of `T⁺` (a model `N` of `T⁺` whose reduct
`Π N = N|Σ` is isomorphic to `M`), and this expansion is unique up to isomorphism. -/
theorem expansion_exists_unique {L : Sig} {T : Theory L} (D : MoritaData L T) (M : Model T) :
    (∃ N : Model D.ext, Nonempty (D.proj.obj N ≅ M)) ∧
      ∀ N N' : Model D.ext, (D.proj.obj N ≅ M) → (D.proj.obj N' ≅ M) → Nonempty (N ≅ N') := by sorry

end MoritaEquiv
