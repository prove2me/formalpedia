-- Prove2me | Theorems.Thm_ManipPotential_proposition_6_11_uniqueness_lipschitz
-- name    : ManipPotential.proposition_6_11_uniqueness_lipschitz
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:24:21.062352+00:00
-- url     : https://prove2.me/theorems/1d5392e5-ffea-472e-9b93-ecb5df9ec1a4
-- title:
--   Proposition 6.11 — uniqueness and the Lipschitz estimate (16)
-- statement:
--   There is a constant $D$ (denoted `L` in the formal statement) such that any two common junctions $P,P'$ in the box, or more generally any two common junctions all of whose coordinates exceed $1$ and whose external coordinates are below $1+1/32$, satisfy
--   $$
--   \|P-P'\|\le D\max\!\left(\max_{s\notin L}|P_s-P'_s|,\;
--   \left|\sum_{j=1}^m P_{\ell_j}-\sum_{j=1}^m P'_{\ell_j}\right|\right).
--   $$
--   The proof uses Lemma 6.10 to compare a coordinatewise maximum of shifted profiles with a ballot obtained from a single external ballot by increasing or decreasing one cyclic coordinate by $1+\kappa$; then Corollary 6.7 supplies the required gap between the cyclic shares corresponding to candidates $1$ and $j$. Setting $N=1+\kappa$ and choosing the scale large enough gives the asserted universal Lipschitz constant.
-- source:
--   Berker–Conitzer–Hartman–Liu–Oesterheld, How Many Votes Is a Lie Worth?, arXiv:2602.22838 (v3, 2026-11-03), proof of Proposition 6.11, uniqueness and Lipschitz estimate (16), pp.34–35.

import Mathlib
import Definitions.Def_ManipPotential_GAxioms
import Definitions.Def_ManipPotential_IsCommonJunction
import Definitions.Def_ManipPotential_ExtRanking
import Definitions.Def_ManipPotential_cycTotal
import Definitions.Def_ManipPotential_kappa

namespace ManipPotential

/-- Proposition 6.11, uniqueness and Lipschitz estimate (16), pp.34--35. -/
theorem proposition_6_11_uniqueness_lipschitz {m : ℕ} [NeZero m] (hm : 3 ≤ m) (K : ℕ)
    (g : (Ranking m → ℚ) → Fin m) (hg : GAxioms K g) :
    ∃ L : NNReal, ∀ P P' : Ranking m → ℝ,
      IsCommonJunction g P → IsCommonJunction g P' →
      (∀ r, 1 < P r) → (∀ r, 1 < P' r) →
      (∀ s : ExtRanking m, P s.1 < 1 + 1 / 32) →
      (∀ s : ExtRanking m, P' s.1 < 1 + 1 / 32) →
      dist P P' ≤ (L : ℝ) *
        max (‖fun s : ExtRanking m => P s.1 - P' s.1‖) |cycTotal P - cycTotal P'| := by sorry
