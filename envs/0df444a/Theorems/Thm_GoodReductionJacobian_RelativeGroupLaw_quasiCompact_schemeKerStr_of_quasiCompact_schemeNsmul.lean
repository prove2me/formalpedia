-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_quasiCompact_schemeKerStr_of_quasiCompact_schemeNsmul
-- name    : GoodReductionJacobian.RelativeGroupLaw.quasiCompact_schemeKerStr_of_quasiCompact_schemeNsmul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/eacfc31e-42cb-50a0-99df-dc08f18c92c7
-- title:
--   Quasi-compactness of the n-torsion over the base
-- statement:
--   Let $R$ be a commutative ring, $A$ a scheme and $f \colon A \to \operatorname{Spec} R$ a morphism, and let $G$ be a `RelativeGroupLaw R f`: that is, for every scheme $T$ and every $t \colon T \to \operatorname{Spec} R$ a multiplication, a unit and an inversion on the set of $T$-points $\{\varphi \colon T \to A \mid \varphi \text{ followed by } f = t\}$, satisfying associativity, the two unit laws and left inversion, together with naturality of the multiplication along any $\psi \colon T' \to T$ with $\psi$ followed by $t$ equal to $t'$ (the operations being transported by precomposition with $\psi$). Let $n$ be a natural number and write $[n] =$ `G.schemeNsmul n` for the underlying morphism $A \to A$ of the $n$-fold $G$-sum of the identity point $\mathbf 1_A$, formed by the recursion $0 \mapsto$ unit, $k+1 \mapsto$ (previous sum) multiplied by the identity point. Assume $[n]$ is quasi-compact. Then the second projection `G.schemeKerStr n`, from the pullback of $[n]$ along the unit section $\operatorname{Spec} R \to A$ attached to $t = \mathrm{id}_{\operatorname{Spec} R}$, to $\operatorname{Spec} R$, is quasi-compact.
--
--   The scheme $A[n]$ is defined as a fibre product, so this records that the structural morphism $A[n] \to \operatorname{Spec} R$ inherits quasi-compactness from multiplication by $n$ on $A$; combined with the corresponding statement for local quasi-finiteness it yields quasi-finiteness in the sense of EGA for the $n$-torsion. It is used in the treatment of Néron objects attached to modular Jacobians at a prime, where torsion subschemes of the identity component must be handled.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_quasiCompact_schemeKerStr_of_quasiCompact_schemeNsmul.lean

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.quasiCompact_schemeKerStr_of_quasiCompact_schemeNsmul
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (G : RelativeGroupLaw R f) (n : ℕ) [QuasiCompact (G.schemeNsmul n)] :
    QuasiCompact (G.schemeKerStr n) := by sorry
