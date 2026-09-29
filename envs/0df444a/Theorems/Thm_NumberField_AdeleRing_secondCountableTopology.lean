-- Prove2me | Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
-- name    : NumberField.AdeleRing.secondCountableTopology
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/7264b0df-f1cc-5f9b-ab85-6de5b82dab3a
-- title:
--   Second countability of the adele ring of a number field
-- statement:
--   Let $K$ be a field equipped with the structure of a number field. The assertion is that the adele ring $\mathbb{A}_K$ of $K$, in the Mathlib model `NumberField.AdeleRing (NumberField.RingOfIntegers K) K` built on the ring of integers $\mathcal{O}_K$ — that is, the product $\bigl(\prod_{v\mid\infty} K_v\bigr)\times\mathbb{A}_K^{\mathrm{fin}}$ of the finite product of the completions of $K$ at its infinite places with the finite adele ring, the latter being the restricted product of the completions $K_v$ at the height-one primes $v$ of $\mathcal{O}_K$ with respect to the subrings of $v$-adic integers, all carried with their standard topologies — satisfies `SecondCountableTopology`: its topology admits a countable base of open sets. No further hypotheses are imposed. The result is stated as a theorem rather than as an instance, so that it may be invoked explicitly as a hypothesis.
--
--   This is the second axiom of countability for $\mathbb{A}_K$, the basic countability property underlying measure-theoretic and exhaustion arguments on adelic spaces; it is used throughout the analytic part of the development, for instance in the integrability and growth estimates for automorphic forms and in the Rankin–Selberg computations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdeleRing_secondCountableTopology.lean

import Mathlib.NumberTheory.NumberField.AdeleRing

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem NumberField.AdeleRing.secondCountableTopology (K : Type*) [Field K] [NumberField K] :
    SecondCountableTopology (NumberField.AdeleRing (NumberField.RingOfIntegers K) K) := by sorry
