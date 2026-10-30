-- Prove2me | Theorems.Thm_JuschenkoMonod_exists_infinite_fg_simple_amenable_and_continuum_many
-- name    : JuschenkoMonod.exists_infinite_fg_simple_amenable_and_continuum_many
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-29T17:29:34.257779+00:00
-- url     : https://prove2.me/theorems/91ba6385-3c67-4a29-ab03-44106cebe435
-- title:
--   Corollary B — there exist infinite, finitely generated, simple, amenable groups, and 2^ℵ₀ pairwise non-isomorphic ones
-- statement:
--   There is a group that is infinite, finitely generated, simple and amenable. Moreover, there is a family $(G_r)_{r \in \mathbf R}$ of groups, each infinite, finitely generated, simple and amenable, with $G_r$ and $G_s$ not isomorphic whenever $r \ne s$.
--
--   *Formalization note.* "There are $2^{\aleph_0}$ nonisomorphic such groups" is stated as a family of pairwise non-isomorphic such groups indexed by $\mathbf R$, a set of cardinality $2^{\aleph_0}$.
-- source:
--   Juschenko, K. and Monod, N., Cantor systems, piecewise translations and simple amenable groups, Ann. of Math. (2) 178 (2013) 775–787, https://doi.org/10.4007/annals.2013.178.2.7, p. 776, Corollary B

import Mathlib
import Definitions.Def_Garrido_Amenability

namespace JuschenkoMonod

theorem exists_infinite_fg_simple_amenable_and_continuum_many :
    (∃ (G : Type) (_ : Group G), Infinite G ∧ Group.FG G ∧ IsSimpleGroup G ∧ Garrido.IsAmenable G) ∧
      ∃ (G : ℝ → Type) (_ : ∀ r, Group (G r)),
        (∀ r, Infinite (G r) ∧ Group.FG (G r) ∧ IsSimpleGroup (G r) ∧ Garrido.IsAmenable (G r)) ∧
        ∀ r s, r ≠ s → IsEmpty (G r ≃* G s) := by
  sorry

end JuschenkoMonod
