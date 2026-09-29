-- Prove2me | Theorems.Thm_NumberField_exists_valuationSubring_eq_localization
-- name    : NumberField.exists_valuationSubring_eq_localization
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/95c89632-a8bf-54a5-a513-d015d275c4fe
-- title:
--   Localisation of ℤ̄ at a maximal ideal is a valuation subring
-- statement:
--   Fix an algebraic closure $\overline{\mathbb{Q}}$ of $\mathbb{Q}$ (Mathlib's `AlgebraicClosure ℚ`) and let $\mathcal{O} = 𝓞\,(\text{AlgebraicClosure }ℚ)$ denote its ring of integers, i.e. the integral closure of $\mathbb{Z}$ in $\overline{\mathbb{Q}}$, the ring of all algebraic integers. Let $Qt$ be an ideal of $\mathcal{O}$ which is assumed maximal (a typeclass hypothesis `Qt.IsMaximal`). The theorem asserts the existence of a valuation subring $A$ of the field $\overline{\mathbb{Q}}$ — that is, a subring with the property that for every $x$ either $x \in A$ or $x^{-1} \in A$ — whose underlying set is described explicitly: for every $x \in \overline{\mathbb{Q}}$, one has $x \in A$ if and only if there exist $s, a \in \mathcal{O}$ with $s \notin Qt$ and $s\,x = a$ in $\overline{\mathbb{Q}}$ (the images of $s$ and $a$ under the inclusion of $\mathcal{O}$ into $\overline{\mathbb{Q}}$ being understood). Thus the localisation $\mathcal{O}_{Qt}$, realised inside $\overline{\mathbb{Q}}$ as the set of fractions with denominator prime to $Qt$, is a valuation ring of $\overline{\mathbb{Q}}$. No uniqueness or further property of $A$ is claimed.
--
--   This is the passage from the ideal-theoretic to the place-theoretic description of the arithmetic of $\overline{\mathbb{Q}}$: a maximal ideal of the ring of all algebraic integers determines a place of $\overline{\mathbb{Q}}$, whose valuation subring is the corresponding localisation. It is used downstream in the treatment of decomposition groups and Frobenius elements, in particular by the statements on existence of Frobenius conjugates and by the characterisation of the valuation subring through the condition that all elements have valuation at most one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_exists_valuationSubring_eq_localization.lean

import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped NumberField Pointwise

theorem NumberField.exists_valuationSubring_eq_localization
    (Qt : Ideal (𝓞 (AlgebraicClosure ℚ))) [Qt.IsMaximal] :
    ∃ A : ValuationSubring (AlgebraicClosure ℚ), ∀ x : AlgebraicClosure ℚ,
      x ∈ A ↔ ∃ s : 𝓞 (AlgebraicClosure ℚ), s ∉ Qt ∧ ∃ a : 𝓞 (AlgebraicClosure ℚ), (s : AlgebraicClosure ℚ) * x = a := by sorry
