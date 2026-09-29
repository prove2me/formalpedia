-- Prove2me | Theorems.Thm_NumberField_mixedEmbedding_coe_dualSubmodule_flip_traceForm_idealLattice
-- name    : NumberField.mixedEmbedding.coe_dualSubmodule_flip_traceForm_idealLattice
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/9fd5cbc5-b006-54a3-976a-a49252021650
-- title:
--   Trace dual of the Minkowski lattice of a fractional ideal
-- statement:
--   Let $K$ be a number field and let $I$ be a unit of the monoid of fractional ideals of $\mathcal{O}_K$ in $K$ (in particular $I \neq 0$). Work in the mixed space $K_{\mathbb{R}} = \mathrm{mixedSpace}\ K$, the product of a copy of $\mathbb{R}$ for each real place and of $\mathbb{C}$ for each complex place, regarded as an $\mathbb{R}$-algebra, with the canonical embedding $\mathrm{mixedEmbedding}\ K \colon K \to K_{\mathbb{R}}$, and let $B(y,z) = \mathrm{Tr}_{K_{\mathbb{R}}/\mathbb{R}}(yz)$ be the trace form of $K_{\mathbb{R}}$ over $\mathbb{R}$. The assertion is an equality of subsets of $K_{\mathbb{R}}$. The left-hand side is the dual submodule, with respect to the flip of $B$, of the $\mathbb{Z}$-submodule $\mathrm{idealLattice}\ K\ I$ obtained as the image of $I$ under the canonical embedding: that is, the set of $z \in K_{\mathbb{R}}$ such that $B(y, z)$ lies in the image of $\mathbb{Z}$ in $\mathbb{R}$ for every $y$ in that lattice. The right-hand side is the image under $\mathrm{mixedEmbedding}\ K$ of the fractional ideal $\mathrm{dual}_{\mathbb{Z},\mathbb{Q}}(I) = \{a \in K : \mathrm{Tr}_{K/\mathbb{Q}}(aI) \subseteq \mathbb{Z}\}$. Since the trace form is symmetric, the flip is immaterial mathematically; it is present because the dual variable of the Mathlib dual submodule occupies the first slot.
--
--   This is the classical identification of the dual lattice of the Minkowski lattice $\sigma(I)$ under the trace pairing with the image of the complementary module $I^{\vee} = \mathfrak{d}_K^{-1} I^{-1}$. It supplies the archimedean half of the self-duality bookkeeping for Poisson summation over a number field, and is used in the adelic Fourier-analysis results on characters given by $\mathrm{Tr}$ and on summation over lattices attached to fractional ideals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_mixedEmbedding_coe_dualSubmodule_flip_traceForm_idealLattice.lean

import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.LinearAlgebra.BilinearForm.DualLattice

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open NumberField NumberField.mixedEmbedding
open scoped Classical nonZeroDivisors

theorem NumberField.mixedEmbedding.coe_dualSubmodule_flip_traceForm_idealLattice
    (K : Type*) [Field K] [NumberField K] (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    (LinearMap.BilinForm.dualSubmodule (Algebra.traceForm ℝ (mixedSpace K)).flip
        (mixedEmbedding.idealLattice K I) : Set (mixedSpace K))
      = mixedEmbedding K '' (FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K) : Set K) := by sorry
