-- Prove2me | Theorems.Thm_IsLocalRing_of_isDomain_of_moduleFinite_of_isAdicComplete
-- name    : IsLocalRing.of_isDomain_of_moduleFinite_of_isAdicComplete
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/c9a098ab-bceb-579d-805d-ba552ec60f56
-- title:
--   A domain module-finite over a complete local ring is local
-- statement:
--   Let $R$ be a commutative ring which is local, Noetherian, and complete with respect to the adic filtration given by its maximal ideal, in the sense that $R$ is both Hausdorff and complete for the $\mathfrak{m}_R$-adic topology, where $\mathfrak{m}_R$ denotes `IsLocalRing.maximalIdeal R`. Let $D$ be a commutative ring which is an integral domain (so nontrivial and without zero divisors), equipped with the structure of an $R$-algebra, and assume that $D$ is finite as an $R$-module, i.e. finitely generated as a module over $R$ via the structure map. The conclusion is that $D$ is again a local ring: $D$ is nontrivial and its nonunits form an additive subgroup, equivalently $D$ has a unique maximal ideal. The domain hypothesis cannot be dropped, as $R \times R$ is module-finite over $R$ without being local.
--
--   This is the standard consequence of Henselianity: a complete Noetherian local ring is Henselian, and over a Henselian local ring every module-finite extension that is a domain is local (equivalently, $\operatorname{Spec}$ of it has a single closed point). In this development it is used to show that Hecke algebras and their quotients arising as module-finite domains over complete local coefficient rings are local, in the construction of Hecke–Galois representation data attached to cusp forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsLocalRing_of_isDomain_of_moduleFinite_of_isAdicComplete.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem IsLocalRing.of_isDomain_of_moduleFinite_of_isAdicComplete (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R] (D : Type*) [CommRing D] [IsDomain D] [Algebra R D] [Module.Finite R D] : IsLocalRing D := by sorry
