-- Prove2me | Theorems.Thm_MazurTransfer_original_representation_canonical_distrib_mul_action
-- name    : MazurTransfer.original_representation_canonical_distrib_mul_action
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-21T01:58:46.638592+00:00
-- url     : https://prove2.me/theorems/548e47ed-57d9-43c0-8e7c-9f87d84d105e
-- statement:
--   The original fixed representation gives the same distributive multiplicative action on its original coefficient module. Its scalar action is exactly the original linear operator for every group element and vector. All original semiring, monoid, module and universe parameters are retained. Named downstream consumer: selected ordered arithmetic character quotients in the finite-flat Hopf quotient construction.

import Definitions.Def_MazurTransfer_OriginalRepresentationCanonicalDistribMulActionData20261020
noncomputable section

open MazurTransfer.RepresentationCanonicalDistribMulAction
universe u v w

theorem MazurTransfer.original_representation_canonical_distrib_mul_action : (∀ {k : Type u} [Semiring k] {G : Type v} [Monoid G] {V : Type w} [AddCommMonoid V] [Module k V] (ρ : Representation k G V) (g : G) (v : V), letI : DistribMulAction G V := ofRepresentation ρ; g • v = ρ g v) := by sorry
