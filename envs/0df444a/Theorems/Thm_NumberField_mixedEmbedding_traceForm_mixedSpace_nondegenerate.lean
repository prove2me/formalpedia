-- Prove2me | Theorems.Thm_NumberField_mixedEmbedding_traceForm_mixedSpace_nondegenerate
-- name    : NumberField.mixedEmbedding.traceForm_mixedSpace_nondegenerate
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/ddef9905-4c6e-5092-a1e7-dbc0de02cde3
-- title:
--   Nondegeneracy of the trace form on the mixed space
-- statement:
--   Let $K$ be a number field, i.e. a field of characteristic zero that is a finite extension of $\mathbb{Q}$. Write $\mathrm{mixedSpace}\ K$ for the mixed (Minkowski) space of $K$, the finite-dimensional commutative $\mathbb{R}$-algebra $\prod_{v \text{ real}} \mathbb{R} \times \prod_{v \text{ complex}} \mathbb{C}$ indexed by the real and by the pairs of conjugate complex places of $K$. The theorem asserts that the trace form of this $\mathbb{R}$-algebra, namely the symmetric $\mathbb{R}$-bilinear form $(y,z) \mapsto \operatorname{Tr}_{\mathrm{mixedSpace}\ K/\mathbb{R}}(yz)$ given by `Algebra.traceForm ℝ (mixedSpace K)`, is nondegenerate in the sense of `LinearMap.BilinForm.Nondegenerate`: if $y \in \mathrm{mixedSpace}\ K$ satisfies $\operatorname{Tr}(yz) = 0$ for every $z \in \mathrm{mixedSpace}\ K$, then $y = 0$.
--
--   This is the base change to $\mathbb{R}$ of the classical nondegeneracy of the trace form of the separable extension $K/\mathbb{Q}$, transported to the Minkowski space $K_{\mathbb{R}} \cong K \otimes_{\mathbb{Q}} \mathbb{R}$. It serves as the input that makes $(y,z) \mapsto \operatorname{Tr}(yz)$ a perfect pairing, and is used in the construction of additive characters and of the Fourier transform on the adeles of $K$, where the self-duality of $\mathrm{mixedSpace}\ K$ is needed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_mixedEmbedding_traceForm_mixedSpace_nondegenerate.lean

import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open NumberField NumberField.mixedEmbedding
open scoped Classical

theorem NumberField.mixedEmbedding.traceForm_mixedSpace_nondegenerate
    (K : Type*) [Field K] [NumberField K] :
    (Algebra.traceForm ℝ (mixedSpace K)).Nondegenerate := by sorry
