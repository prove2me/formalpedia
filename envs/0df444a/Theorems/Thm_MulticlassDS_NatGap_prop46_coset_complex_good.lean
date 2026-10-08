-- Prove2me | Theorems.Thm_MulticlassDS_NatGap_prop46_coset_complex_good
-- name    : MulticlassDS.NatGap.prop46_coset_complex_good
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T15:48:57.521992+00:00
-- url     : https://prove2.me/theorems/4e56e49c-d8cd-4c6a-bead-e0477535f918
-- title:
--   Proposition 46, p. 31 — the coset complex of Theorem 45 has dimension d − 1, is good and has no empty squares
-- statement:
--   Let $F$ be a finite group, $d > 1$, and $H_1, \dots, H_d \le F$ subgroups such that
--
--   1. $\big(\bigcap_{j \neq i} H_j\big) \setminus H_i \neq \emptyset$ for every $i \in [d]$, and
--   2. the coset complex $C = C_F(H_1, \dots, H_d)$ contains no empty square.
--
--   Then $C$ has dimension $d - 1$, is good (finite, pure, properly colorable with $d$ colors, and satisfies replacement), and has no empty squares.
--
--   This is the step that turns the group-theoretic construction of Theorem 45 into a good complex, from which Proposition 42 produces a $d$-dimensional pseudo-cube.
--
--   **Formalization Note** The hypotheses are exactly "as in Theorem 45". The dimension is $d - 1$ with natural-number subtraction, which is exact because $d > 1$; the coloring then takes values in `Fin (d - 1 + 1)`, i.e. $d$ colors.
-- source:
--   Brukhim, Carmon, Dinur, Moran, Yehudayoff, A Characterization of Multiclass Learnability, arXiv:2203.01550v1, p. 31, Proposition 46

import Mathlib
import Definitions.Def_MulticlassDS_NatGap_Dimensions
import Definitions.Def_MulticlassDS_NatGap_Complexes

namespace MulticlassDS.NatGap

theorem prop46_coset_complex_good {F : Type*} [Group F] [Finite F] (d : ℕ) (hd : 1 < d)
    (Hs : Fin d → Subgroup F)
    (h1 : ∀ i : Fin d, ∃ z : F, (∀ j : Fin d, j ≠ i → z ∈ Hs j) ∧ z ∉ Hs i)
    (h2 : NoEmptySquares (cosetComplex Hs)) :
    IsGood (cosetComplex Hs) (d - 1) ∧ NoEmptySquares (cosetComplex Hs) := by sorry

end MulticlassDS.NatGap
