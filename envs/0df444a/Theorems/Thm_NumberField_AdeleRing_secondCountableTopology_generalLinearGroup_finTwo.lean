-- Prove2me | Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
-- name    : NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/6b7f5e32-fbfb-5451-8d39-6f080b8c7071
-- title:
--   GL₂ of the adeles is second countable
-- statement:
--   Let $K$ be a field equipped with a number field structure, and let $\mathbb{A}_K$ denote the adele ring of $K$ over its ring of integers $\mathcal{O}_K$, with its usual topology (the product of the archimedean completions with the finite adele ring). Form the general linear group $\mathrm{GL}_2(\mathbb{A}_K)$, realised in Mathlib as the unit group of the ring $M_2(\mathbb{A}_K)$ of $2\times 2$ matrices indexed by `Fin 2`, carrying the unit-group topology, that is, the topology induced by the embedding $g \mapsto (g, g^{-1})$ into $M_2(\mathbb{A}_K) \times M_2(\mathbb{A}_K)^{\mathrm{op}}$ rather than the subspace topology from $M_2(\mathbb{A}_K)$. The assertion is that this topological space is second countable, i.e. its topology admits a countable base. The statement carries no hypotheses beyond $K$ being a number field; it records the instance `SecondCountableTopology` for $\mathrm{GL}_2(\mathbb{A}_K)$ in the form of a theorem.
--
--   This is the second countability of the adelic group $\mathrm{GL}_2(\mathbb{A}_K)$, the standing countability input for $\sigma$-compactness and countable exhaustion arguments on $\mathrm{GL}_2(\mathbb{A}_K)$; it is invoked widely in the measure-theoretic and integrability parts of the automorphic forms development, for instance in establishing almost-everywhere integrability of constant-term integrands from local integrability.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo.lean

import Mathlib.NumberTheory.NumberField.AdeleRing

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo (K : Type*) [Field K]
    [NumberField K] :
    SecondCountableTopology
      (Matrix.GeneralLinearGroup (Fin 2) (NumberField.AdeleRing (NumberField.RingOfIntegers K) K)) := by sorry
