-- Prove2me | Theorems.Thm_MulticlassDS_NatGap_theorem45_coset_complex
-- name    : MulticlassDS.NatGap.theorem45_coset_complex
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T15:48:39.315968+00:00
-- url     : https://prove2.me/theorems/2c6e14f4-aa19-46c5-95de-d37b32b45b7a
-- title:
--   Theorem 45, p. 30 (Januszkiewicz–Świątkowski) — finite groups whose coset complexes have no empty squares
-- statement:
--   This is a result of Januszkiewicz and Świątkowski (*Hyperbolic Coxeter groups of large dimension*, Comment. Math. Helv. 78 (2003)), stated in this form as Theorem 45 of the paper.
--
--   For every integer $d > 1$ there exist a finite group $F$ and subgroups $H_1, \dots, H_d \le F$ such that
--
--   1. for every $i \in [d]$,
--   $$\Big(\bigcap_{j \neq i} H_j\Big) \setminus H_i \neq \emptyset ;$$
--   2. the coset complex $C_F(H_1, \dots, H_d)$ contains no empty square.
--
--   These are the two properties the paper needs to obtain, for every $d$, a pseudo-cube of dimension $d$ with Natarajan dimension 1. The construction is finite: infinite complexes with the corresponding properties are easy to build.
--
--   **Formalization Note** The subgroups are indexed by `Fin d`. The group is existentially quantified in `Type` together with its `Group` structure, and finiteness is `Finite F`.
-- source:
--   Brukhim, Carmon, Dinur, Moran, Yehudayoff, A Characterization of Multiclass Learnability, arXiv:2203.01550v1, p. 30, Theorem 45 (Januszkiewicz and Świątkowski 2003)

import Mathlib
import Definitions.Def_MulticlassDS_NatGap_Dimensions
import Definitions.Def_MulticlassDS_NatGap_Complexes

namespace MulticlassDS.NatGap

theorem theorem45_coset_complex (d : ℕ) (hd : 1 < d) :
    ∃ (F : Type) (_ : Group F), Finite F ∧ ∃ Hs : Fin d → Subgroup F,
      (∀ i : Fin d, ∃ z : F, (∀ j : Fin d, j ≠ i → z ∈ Hs j) ∧ z ∉ Hs i) ∧
        NoEmptySquares (cosetComplex Hs) := by sorry

end MulticlassDS.NatGap
