-- Prove2me | Theorems.Thm_MazurTransfer_Order13LocalRingInValuationSubring_local_coefficients_mem
-- name    : MazurTransfer.Order13LocalRingInValuationSubring.local_coefficients_mem
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T03:43:21.334822+00:00
-- url     : https://prove2.me/theorems/add373ce-3c4e-42e4-903b-f833286a7bb6
-- title:
--   The local integer coefficient image lies in a valuation ring above the prime
-- statement:
--   Let $q$ be prime, let $\Omega$ be a field with the original algebra over $\mathbb Z_{(q)}$, and let $A\subseteq\Omega$ be a valuation subring in which $q$ is a nonunit. Then every coefficient has image in $A$:
--
--   $$
--   \operatorname{im}(\mathbb Z_{(q)}\longrightarrow\Omega)\subseteq A.
--   $$
--
--    The field is not assumed to have characteristic zero. Named downstream consumer: the coefficient-ring hypothesis for genuine inertia-fixed norm lifts.
-- source:
--   Original MazurTheorem Order13LocalRingInValuationSubring.local_coefficients_mem, Apache-2.0. Full original local-algebra telescope is retained explicitly.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the canonical local integer coefficient ring is contained
in every valuation subring lying over the specified rational prime.
Named downstream consumer: inertia fixed lifts for integral order-13 norms.
-/
import Definitions.Def_MazurTransfer_Order13LocalIntegralCoefficientMaps
import Definitions.Def_FLTPrelim_Ramification
import Mathlib.RingTheory.Ideal.Int

noncomputable section
open MazurTransfer
open Order13LocalIntegralCoefficientMaps

theorem MazurTransfer.Order13LocalRingInValuationSubring.local_coefficients_mem (q : ℕ) [Fact q.Prime] {Ω : Type} [Field Ω]
    [Algebra (LocalRing q) Ω] (A : ValuationSubring Ω) (hA : A.LiesOverPrime q)
    (r : LocalRing q) : algebraMap (LocalRing q) Ω r ∈ A := by sorry
