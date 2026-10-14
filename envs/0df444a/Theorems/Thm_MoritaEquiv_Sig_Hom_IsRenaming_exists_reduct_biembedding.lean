-- Prove2me | Theorems.Thm_MoritaEquiv_Sig_Hom_IsRenaming_exists_reduct_biembedding
-- name    : MoritaEquiv.Sig.Hom.IsRenaming.exists_reduct_biembedding
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-13T20:02:40.37788+00:00
-- url     : https://prove2.me/theorems/f6871e86-d504-481a-ad15-ac85c3243f1e
-- title:
--   Every structure is bi-embeddable with a reduct along a renaming
-- statement:
--   Let $F:\Sigma\to\Sigma'$ be a renaming of many-sorted signatures, i.e. a signature morphism that is bijective on sorts and, for each arity, bijective on function and relation symbols.
--
--   **Statement.** For every $\Sigma$-structure $N$ there is a $\Sigma'$-structure $M$ whose $F$-reduct $M|_F$ admits elementary embeddings $M|_F\to N$ and $N\to M|_F$.
--
--   The structure $M$ is built by transporting $N$ along $F^{-1}$ (the carrier of sort $s'$ is $N_{F^{-1}(s')}$). Its reduct is then strongly isomorphic to $N$, so it is elementarily equivalent to $N$ in both directions. This is the "essential surjectivity" half of the fact that the reduct along a renaming is an equivalence of model categories.
--
--   **Formalization Note** The conclusion asks only for elementary embeddings in both directions (both are in fact induced by mutually inverse bijections).
-- source:
--   T. W. Barrett, H. Halvorson, Morita Equivalence, Rev. Symb. Logic 9 (2016) 556-582, https://arxiv.org/abs/1506.04675, §4-§5 (used for the second half of Theorem 5.2)

import Mathlib
import Definitions.Def_MoritaEquiv_defs

open CategoryTheory

namespace MoritaEquiv

/-- Every structure is, up to elementary embeddings in both directions, a reduct along a renaming:
if `F : L ⟶ L'` is a renaming, then for every `L`-structure `N` there is an `L'`-structure `M`
whose `F`-reduct admits elementary embeddings to and from `N`. -/
theorem Sig.Hom.IsRenaming.exists_reduct_biembedding {L L' : Sig} {F : L.Hom L'}
    (hF : F.IsRenaming) (N : Str L) :
    ∃ M : Str L', Nonempty (ElemEmb (M.reduct F) N) ∧ Nonempty (ElemEmb N (M.reduct F)) := by sorry

end MoritaEquiv
