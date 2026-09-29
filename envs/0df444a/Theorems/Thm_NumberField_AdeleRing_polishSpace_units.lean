-- Prove2me | Theorems.Thm_NumberField_AdeleRing_polishSpace_units
-- name    : NumberField.AdeleRing.polishSpace_units
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/81255953-4646-510c-8911-3c6debfebfdd
-- title:
--   The idele group of a number field is Polish
-- statement:
--   Let $K$ be a number field: a type $K$ (in `Type`) carrying a field structure together with a `NumberField` structure, so $K$ is of characteristic zero and finite-dimensional over $\mathbb{Q}$. Form the adele ring `AdeleRing (𝓞 K) K` of $K$ relative to its ring of integers $\mathcal{O}_K$, i.e. the product of the finite adeles (the restricted product over the finite places, with respect to the completions of $\mathcal{O}_K$) with the infinite adeles, and let $(\mathbb{A}_K)^\times$ denote its group of units, equipped with the Mathlib topology on a unit group, namely the topology induced by the embedding $u \mapsto (u, u^{-1})$ of `Units.embedProduct` into $\mathbb{A}_K \times \mathbb{A}_K^{\mathrm{op}}$. The theorem asserts that this topological group is a Polish space: its topology is second countable and is induced by some complete metric. No further hypotheses on $K$ are imposed.
--
--   This is the standard topological regularity statement for the idele group $\mathbb{A}_K^\times$ of a number field, the multiplicative companion of the corresponding assertion for the adele ring itself. It supplies the descriptive-set-theoretic hypotheses needed for measure-theoretic arguments on the idele group, and is used in the approximation of $L^p$ functions on $\mathbb{A}_K^\times$ by continuous functions in the analytic theory of automorphic forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdeleRing_polishSpace_units.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField

theorem NumberField.AdeleRing.polishSpace_units (K : Type) [Field K] [NumberField K] :
    PolishSpace (AdeleRing (𝓞 K) K)ˣ := by sorry
