-- Prove2me | Theorems.Thm_MoritaEquiv_proj_full
-- name    : MoritaEquiv.proj_full
-- status  : Open
-- author  : @Alien60
-- created : 2026-10-10T12:58:24.575488+00:00
-- url     : https://prove2.me/theorems/379e1b83-dbea-43a9-8c28-6c636cc01089
-- title:
--   The reduct functor Π is full
-- statement:
--   Throughout: many-sorted first-order logic with nonempty sorts; $\mathrm{Mod}(T)$ has the models of $T$ as objects and elementary embeddings as arrows; $D$ is a Morita extension of the $\Sigma$-theory $T$ (new product, coproduct, subsort and quotient sorts and explicitly defined symbols, with admissibility in every model of $T$), $T^+$ the extended theory and $\Pi:\mathrm{Mod}(T^+)\to\mathrm{Mod}(T)$ the reduct functor. $\Pi$ is full: every elementary embedding $\Pi N\to\Pi N'$ is the restriction of an elementary embedding $N\to N'$.
-- source:
--   T. W. Barrett, H. Halvorson, Morita Equivalence, Rev. Symb. Logic 9 (2016) 556-582, https://arxiv.org/abs/1506.04675 (numbering as in arXiv v1), §5, Proposition 5.3 (with Lemma 4.1)

import Mathlib
import Definitions.Def_MoritaEquiv_defs

open CategoryTheory

namespace MoritaEquiv

/-- Barrett–Halvorson, Proposition 5.3: for a Morita extension `T⁺` of `T`, the reduct functor
`Π : Mod(T⁺) ⥤ Mod(T)` is full: every elementary embedding `M|Σ → N|Σ` between reducts of
models of `T⁺` extends to an elementary embedding `M → N`. -/
theorem proj_full {L : Sig} {T : Theory L} (D : MoritaData L T) : D.proj.Full := by sorry

end MoritaEquiv
