-- Prove2me | Theorems.Thm_MazurRapoportAppendix_SpecialFibreComponentTable_mem_range_intersectionAlpha_iff_comp_of_inter_equiv
-- name    : MazurRapoportAppendix.SpecialFibreComponentTable.mem_range_intersectionAlpha_iff_comp_of_inter_equiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/b8ddfb36-27ab-5228-acf7-7034e98c79fe
-- title:
--   Transport of imα along an intersection-preserving reindexing
-- statement:
--   Let $\iota$ and $\iota'$ be finite types and let $t$, $t'$ be special-fibre component tables on them: each such table consists of a multiplicity function $\mathrm{mult}\colon \iota \to \mathbb{N}$ and an intersection function $\mathrm{inter}\colon \iota \to \iota \to \mathbb{Z}$, subject to positivity of all multiplicities, symmetry $\mathrm{inter}\,i\,j = \mathrm{inter}\,j\,i$, and the fibre relation $\sum_j (\mathrm{inter}\,i\,j)\cdot \mathrm{mult}\,j = 0$ for every $i$. Let $\Phi\colon \iota \simeq \iota'$ be a bijection which matches the intersection functions, $t'.\mathrm{inter}\,(\Phi a)\,(\Phi b) = t.\mathrm{inter}\,a\,b$ for all $a,b$; no compatibility of the multiplicities along $\Phi$ is assumed. Write $\alpha_t$ for the additive endomorphism `intersectionAlpha t` of $\iota \to \mathbb{Z}$ given by $(\alpha_t c)_j = \sum_i c_i \cdot (t.\mathrm{inter}\,i\,j)$, and similarly $\alpha_{t'}$. Then for every $f\colon \iota' \to \mathbb{Z}$, the vector $f$ lies in the range of $\alpha_{t'}$ if and only if $f \circ \Phi$ lies in the range of $\alpha_t$.
--
--   The subgroup $\operatorname{im}\alpha_t$ is one half of the combinatorial presentation of the component group of a Néron model in terms of the intersection matrix of the special fibre; this lemma says that membership in it depends only on the intersection table up to relabelling of components. It is used in the construction of the degree/multidegree comparison for Deligne–Rapoport models, where a multidegree vector computed on a geometric model must be transported to a combinatorially indexed table.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MazurRapoportAppendix_SpecialFibreComponentTable_mem_range_intersectionAlpha_iff_comp_of_inter_equiv.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_MazurRapoportAppendixPicNeronCarriers

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MazurRapoportAppendix
open scoped BigOperators

theorem MazurRapoportAppendix.SpecialFibreComponentTable.mem_range_intersectionAlpha_iff_comp_of_inter_equiv
    {ι ι' : Type*} [Fintype ι] [Fintype ι']
    (t : SpecialFibreComponentTable ι) (t' : SpecialFibreComponentTable ι') (Φ : ι ≃ ι')
    (hΦ : ∀ a b, t'.inter (Φ a) (Φ b) = t.inter a b) (f : ι' → ℤ) :
    f ∈ (intersectionAlpha t').range ↔ (f ∘ Φ) ∈ (intersectionAlpha t).range := by sorry
