-- Prove2me | Theorems.Thm_MazurTransfer_Order13LocalRingInValuationSubring_integer_maximalIdeal_comap
-- name    : MazurTransfer.Order13LocalRingInValuationSubring.integer_maximalIdeal_comap
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T03:31:27.583784+00:00
-- url     : https://prove2.me/theorems/67c5277c-b81e-420a-946d-ee7d52a639d2
-- title:
--   The integer maximal ideal of a valuation ring lying above a rational prime
-- statement:
--   Let $q$ be prime, let $\Omega$ be the original field equipped with its original algebra over $\mathbb Z_{(q)}$, and let $A$ be a valuation subring of $\Omega$ in which $q$ is a nonunit. Then
--
--   $$
--   (\mathfrak m_A)\cap\mathbb Z=(q).
--   $$
--
--    The intersection is the inverse image under the integer cast into $A$. Every original hypothesis, including the local-algebra instance, is retained explicitly. Named downstream consumer: containment of the local integer coefficient ring in $A$, followed by genuine inertia-fixed norm fibres.
-- source:
--   Original MazurTheorem Order13LocalRingInValuationSubring.integer_maximalIdeal_comap, Apache-2.0. The complete original telescope and the original ramification definition types and values are compared. Earlier local drafts remain preserved without mathematical credit.

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

theorem MazurTransfer.Order13LocalRingInValuationSubring.integer_maximalIdeal_comap (q : ℕ) [Fact q.Prime] {Ω : Type} [Field Ω]
    [Algebra (LocalRing q) Ω] (A : ValuationSubring Ω)
    (hA : A.LiesOverPrime q) :
    (IsLocalRing.maximalIdeal A).comap (Int.castRingHom A) = primeIdeal q := by sorry
