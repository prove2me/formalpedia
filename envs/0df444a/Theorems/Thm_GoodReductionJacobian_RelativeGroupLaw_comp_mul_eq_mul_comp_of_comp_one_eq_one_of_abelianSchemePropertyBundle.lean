-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_comp_mul_eq_mul_comp_of_comp_one_eq_one_of_abelianSchemePropertyBundle
-- name    : GoodReductionJacobian.RelativeGroupLaw.comp_mul_eq_mul_comp_of_comp_one_eq_one_of_abelianSchemePropertyBundle
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/d5e0df1d-5a8e-5575-8647-150428ed0857
-- title:
--   Rigidity: unit-preserving maps to abelian varieties are homomorphisms
-- statement:
--   Let $k$ be a field and let $f : G \to \operatorname{Spec} k$ be a separated, quasi-compact, smooth morphism of schemes whose source $G$ is a connected topological space. Let $L$ be a relative group law for $f$: for every scheme $T$ and every $t : T \to \operatorname{Spec} k$ it equips the set of sections $\{x : T \to G \mid x \circ f = t\}$ with multiplication, unit and inversion operations satisfying associativity, the two unit laws and left inverse, and compatible with precomposition by morphisms $\psi : T' \to T$ with $\psi$ followed by $t$ equal to $t'$. Let $f_A : A \to \operatorname{Spec} k$ carry a relative group law $L_A$, and assume the bundle of properties $\mathrm{AbelianSchemePropertyBundle}$ for $f_A$: $f_A$ is smooth and proper, the preimage under $f_A$ of each point of $\operatorname{Spec} k$ is connected and nonempty, and $f_A$ admits some relative group law. Let $\varphi : G \to A$ satisfy $\varphi$ followed by $f_A$ equals $f$, and assume that the unit section $L.\mathrm{one}$ over $\mathrm{id}_{\operatorname{Spec} k}$, followed by $\varphi$, is the unit section $L_A.\mathrm{one}$ over $\mathrm{id}_{\operatorname{Spec} k}$. Then for every scheme $T$, every $t : T \to \operatorname{Spec} k$ and all sections $x, y$ of $f$ over $t$, the section $L.\mathrm{mul}\ t\ x\ y$ followed by $\varphi$ equals $L_A.\mathrm{mul}\ t$ applied to $x$ followed by $\varphi$ and $y$ followed by $\varphi$.
--
--   This is the rigidity statement that a $k$-morphism from a connected smooth group scheme to an abelian variety carrying the unit to the unit is a homomorphism, in the form where the source is not assumed proper. It is used in the construction of the group law and endomorphisms on Néron models and Jacobians, for instance by the results on composing sections with a unit-preserving morphism and on realising iterated compositions as multiples of a section.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_comp_mul_eq_mul_comp_of_comp_one_eq_one_of_abelianSchemePropertyBundle.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.comp_mul_eq_mul_comp_of_comp_one_eq_one_of_abelianSchemePropertyBundle
    (k : Type u) [Field k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)}
    [IsSeparated f] [QuasiCompact f] [Smooth f] [ConnectedSpace G] (L : RelativeGroupLaw k f)
    {A : Scheme.{u}} {fA : A ⟶ Spec (CommRingCat.of k)} (LA : RelativeGroupLaw k fA)
    (hA : AbelianSchemePropertyBundle k fA) (φ : SchemeHomOver f fA)
    (hφ : NeronModelInfra.schemeHomOverComp (L.one (𝟙 (Spec (CommRingCat.of k)))) φ =
      LA.one (𝟙 (Spec (CommRingCat.of k)))) :
    ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t f),
      NeronModelInfra.schemeHomOverComp (L.mul t x y) φ =
        LA.mul t (NeronModelInfra.schemeHomOverComp x φ) (NeronModelInfra.schemeHomOverComp y φ) := by sorry
