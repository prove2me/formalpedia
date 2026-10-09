-- Prove2me | Theorems.Thm_NicerEars_TJoin_corollary_14
-- name    : NicerEars.TJoin.corollary_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:27:36.804485+00:00
-- url     : https://prove2.me/theorems/42583043-4bc3-4f7e-a066-9426a0865734
-- title:
--   Corollary 14 (Lovász) — min-max formula for forest representative systems
-- statement:
--   (Lovász 1970.) Let $U$ and $M$ be finite sets and $\emptyset\ne U_f\subseteq U$ for $f\in M$. Then the maximum cardinality of a subset $F\subseteq M$ for which $(U_f)_{f\in F}$ has a forest representative system equals
--   $$\min\Bigl\{\,|M|-\sum_{W\in\mathcal W}\bigl(|\{f\in M: U_f\subseteq W\}|-(|W|-1)\bigr)\ :\ \mathcal W\text{ is a partition of }U\Bigr\}.$$
--
--   Applied with $U=V(G)\setminus V_M$ and $U_f$ the endpoint sets of $\mathcal P_f$, it yields the earmuff theorem (Theorem 18).
--
--   **Formalization Note.** "Maximum = minimum" is stated as: every $F$ with a forest representative system has $|F|$ at most the bracket for every partition, and some such $F$ and some partition attain equality. Arithmetic is in $\mathbb Z$.
-- source:
--   Sebő and Vygen, Shorter tours by nicer ears, arXiv:1201.1870v3, p. 12, Corollary 14 (Lovász [1970])

import Mathlib
import Definitions.Def_NicerEars_TJoin_ForestRep

namespace NicerEars.TJoin

open Finset

/-- Corollary 14 (Lovász [1970]; p. 12): for finite sets `U`, `M` and `∅ ≠ U_f ⊆ U` (`f ∈ M`), the
maximum cardinality of a subset `F ⊆ M` for which `(U_f)_{f ∈ F}` has a forest representative system
equals
`min { |M| − Σ_{W ∈ 𝒲} (|{f ∈ M : U_f ⊆ W}| − (|W| − 1)) : 𝒲 a partition of U }`,
stated as: every such `F` is bounded by the bracket for every partition, and some such `F` and some
partition attain equality (computed in `ℤ`). -/
theorem corollary_14 {U M : Type} [Fintype U] [DecidableEq U] [Fintype M] [DecidableEq M]
    (Uf : M → Finset U) (hUf : ∀ f, (Uf f).Nonempty) :
    (∀ F : Finset M, HasForestRepSystem Uf F → ∀ 𝒲 : Finpartition (univ : Finset U),
      (#F : ℤ) ≤ (Fintype.card M : ℤ) -
        ∑ W ∈ 𝒲.parts, ((#(univ.filter (fun f => Uf f ⊆ W)) : ℤ) - ((#W : ℤ) - 1))) ∧
    ∃ F : Finset M, HasForestRepSystem Uf F ∧ ∃ 𝒲 : Finpartition (univ : Finset U),
      (#F : ℤ) = (Fintype.card M : ℤ) -
        ∑ W ∈ 𝒲.parts, ((#(univ.filter (fun f => Uf f ⊆ W)) : ℤ) - ((#W : ℤ) - 1)) := by sorry

end NicerEars.TJoin
