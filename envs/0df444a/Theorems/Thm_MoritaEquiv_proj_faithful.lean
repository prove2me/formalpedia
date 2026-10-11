-- Prove2me | Theorems.Thm_MoritaEquiv_proj_faithful
-- name    : MoritaEquiv.proj_faithful
-- status  : Open
-- author  : @Alien60
-- created : 2026-10-10T12:57:50.640054+00:00
-- url     : https://prove2.me/theorems/5fc1ebb2-faf2-4603-844a-7d08540bd878
-- title:
--   The reduct functor Π is faithful
-- statement:
--   Throughout: many-sorted first-order logic with nonempty sorts; $\mathrm{Mod}(T)$ has the models of $T$ as objects and elementary embeddings as arrows; $D$ is a Morita extension of the $\Sigma$-theory $T$ (new product, coproduct, subsort and quotient sorts and explicitly defined symbols, with admissibility in every model of $T$), $T^+$ the extended theory and $\Pi:\mathrm{Mod}(T^+)\to\mathrm{Mod}(T)$ the reduct functor. $\Pi$ is faithful: an elementary embedding of models of $T^+$ is determined by its restriction to the old sorts.
-- source:
--   T. W. Barrett, H. Halvorson, Morita Equivalence, Rev. Symb. Logic 9 (2016) 556-582, https://arxiv.org/abs/1506.04675 (numbering as in arXiv v1), §5, Proposition 5.2

import Mathlib
import Definitions.Def_MoritaEquiv_defs

open CategoryTheory

namespace MoritaEquiv

/-- Barrett–Halvorson, Proposition 5.2: for a Morita extension `T⁺` of `T`, the reduct functor
`Π : Mod(T⁺) ⥤ Mod(T)` is faithful. -/
theorem proj_faithful {L : Sig} {T : Theory L} (D : MoritaData L T) : D.proj.Faithful := by sorry

end MoritaEquiv
