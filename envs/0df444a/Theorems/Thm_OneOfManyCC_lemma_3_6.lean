-- Prove2me | Theorems.Thm_OneOfManyCC_lemma_3_6
-- name    : OneOfManyCC.lemma_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:52:47.23798+00:00
-- url     : https://prove2.me/theorems/eb3b55a5-9476-4c42-b837-8f6f670979f0
-- title:
--   Lemma 3.6 (von Neumann) — minimax in threshold form for a relation $C\subseteq\mathcal H\times\mathcal Z$
-- statement:
--   Let $\mathcal H$ and $\mathcal Z$ be finite nonempty sets, let $C\subseteq\mathcal H\times\mathcal Z$, and let $\delta\in\mathbb R$. If for every distribution $\pi$ on $\mathcal Z$ some $H\in\mathcal H$ satisfies
--
--   $$\Pr_{z\sim\pi}[(H,z)\in C]\ge\delta,$$
--
--   then some distribution $\Lambda$ on $\mathcal H$ satisfies
--
--   $$\Pr_{H\sim\Lambda}[(H,z)\in C]\ge\delta\quad\text{for every }z\in\mathcal Z.$$
--
--   This is the form of the minimax theorem for zero-sum games used to pass from a good response to each distribution to one mixture good against all points.
--
--   Differences from the source:
--   - encoding: a distribution on a finite set → a point of `stdSimplex ℝ X`, with $\mu(E)$ as `mass μ E`; reason: nonnegative weights summing to one; the probability of an event is the sum of its weights
--   - encoding: finite nonempty sets $\mathcal H,\mathcal Z$ → Fintype and Nonempty types in `Type`; reason: every finite set is equivalent to a type in `Type`
-- source:
--   Chukhin, Kulikov, Mihajlin, Smal, Solving One of Many Instances Is Almost as Hard as Solving One, STOC 2027 submission (manuscript sha256 5d4d41dd…), Lemma 3.6, p.8

import Mathlib
import Definitions.Def_OneOfManyCC_mass

namespace OneOfManyCC

/-- **Lemma 3.6 (von Neumann minimax), in threshold form.**
Chukhin, Kulikov, Mihajlin, Smal, *Solving One of Many Instances Is Almost as Hard as Solving One*, STOC 2027 submission (manuscript sha256 5d4d41dd…), Lemma 3.6, p.8:
"Let H and Z be finite nonempty sets, let C ⊆ H × Z, and let δ ∈ R. If for every distribution π on Z
some H ∈ H satisfies Pr_{z∼π}[(H, z) ∈ C] ≥ δ, then some distribution Λ on H satisfies
Pr_{H∼Λ}[(H, z) ∈ C] ≥ δ for every z ∈ Z."

**Formalization Note.** `δ` is any real number, as printed. -/
theorem lemma_3_6 {H Z : Type} [Fintype H] [Nonempty H] [Fintype Z] [Nonempty Z]
    (C : H → Z → Prop) (δ : ℝ)
    (h : ∀ π ∈ stdSimplex ℝ Z, ∃ H₀ : H, δ ≤ mass π {z | C H₀ z}) :
    ∃ Λ ∈ stdSimplex ℝ H, ∀ z, δ ≤ mass Λ {H₀ | C H₀ z} := by sorry

end OneOfManyCC
