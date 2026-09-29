-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_schemeKerStr_props_of_schemeNsmul
-- name    : GoodReductionJacobian.RelativeGroupLaw.schemeKerStr_props_of_schemeNsmul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/c0c414ab-bf8e-5619-8b5c-8fae2a47f852
-- title:
--   Properties of the n-torsion kernel of a relative group law
-- statement:
--   Let $R$ be a commutative ring and let $g\colon G \to \operatorname{Spec} R$ be a separated, quasi-compact morphism of schemes. Let $L$ be a relative group law for $g$, that is, a rule assigning to every $t\colon T \to \operatorname{Spec} R$ a group structure (multiplication, unit, inversion, with associativity, both unit laws and left inverses) on the set of relative points $\{\varphi\colon T \to G \mid \varphi \circ g = t\}$, the multiplication being natural under precomposition with morphisms $\psi\colon T' \to T$ satisfying $\psi$ followed by $t$ equal to $t'$. Let $n$ be a natural number and write $[n] :=$ `L.schemeNsmul n` for the $G$-endomorphism obtained as the underlying morphism of the $n$-th power, in the group on relative points over $g$ itself, of the identity point $\langle \mathbf{1}_G, \cdot\rangle$ (the power being formed by recursion, with the unit for $n = 0$). Assume $[n]$ is locally quasi-finite and flat. Let $e := (L.\mathrm{one}\,(\mathbf{1}_{\operatorname{Spec} R})).1\colon \operatorname{Spec} R \to G$ be the underlying morphism of the unit point over the identity of $\operatorname{Spec} R$, and let the kernel be the fibre product of $[n]$ and $e$, with structure morphism the second projection to $\operatorname{Spec} R$. Then this structure morphism is locally quasi-finite, quasi-compact, flat and separated; $e$ is a closed immersion; the first projection from the kernel to $G$ is a closed immersion; and if $g$ is smooth then $g$ is locally of finite type.
--
--   This is the bookkeeping statement that the $n$-torsion subscheme $G[n]$, realised as the fibre product of multiplication by $n$ with the unit section, is a quasi-finite flat separated quasi-compact $R$-scheme sitting in $G$ as a closed subscheme. It supplies exactly the hypotheses needed later for the analysis of $G[n]$ over a henselian local base: it is used in the lifting of points on the torus fibre of a split torus, and in the torsion statements for Néron objects attached to modular curves at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_schemeKerStr_props_of_schemeNsmul.lean

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing TensorProduct

theorem GoodReductionJacobian.RelativeGroupLaw.schemeKerStr_props_of_schemeNsmul
    {R : Type u} [CommRing R] {G : Scheme.{u}} (g : G ⟶ Spec (CommRingCat.of R)) [IsSeparated g] [QuasiCompact g]
    (L : RelativeGroupLaw R g) (n : ℕ)
    (hqf : LocallyQuasiFinite (L.schemeNsmul n)) (hfl : Flat (L.schemeNsmul n)) :
    LocallyQuasiFinite (L.schemeKerStr n) ∧ QuasiCompact (L.schemeKerStr n) ∧ Flat (L.schemeKerStr n) ∧
      IsSeparated (L.schemeKerStr n) ∧
      IsClosedImmersion (L.one (𝟙 (Spec (CommRingCat.of R)))).1 ∧
      IsClosedImmersion (pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1) ∧
      (Smooth g → LocallyOfFiniteType g) := by sorry
