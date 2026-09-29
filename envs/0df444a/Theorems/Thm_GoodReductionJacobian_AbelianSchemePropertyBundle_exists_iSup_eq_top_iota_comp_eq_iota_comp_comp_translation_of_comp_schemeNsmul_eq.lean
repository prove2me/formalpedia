-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_iSup_eq_top_iota_comp_eq_iota_comp_comp_translation_of_comp_schemeNsmul_eq
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.exists_iSup_eq_top_iota_comp_eq_iota_comp_comp_translation_of_comp_schemeNsmul_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/41400705-ff2f-53bd-b63e-f5504c469a1a
-- title:
--   Maps equal after [n] differ locally by n-torsion translation
-- statement:
--   Let $k$ be an algebraically closed field, let $f : A \to \operatorname{Spec} k$ be a morphism of schemes, and let $L$ be a relative group law for $f$: a rule giving, for every $t : T \to \operatorname{Spec} k$, a group structure (multiplication, unit, inverse, with associativity, both unit laws and left inverse) on the set of $\varphi : T \to A$ with $\varphi$ followed by $f$ equal to $t$, natural under precomposition with any $\psi : T' \to T$ satisfying $\psi$ followed by $t$ equals $t'$. Assume $L$ is commutative, and that $f$ satisfies the property bundle $\mathtt{AbelianSchemePropertyBundle}$, i.e. $f$ is smooth and proper, each fibre $f^{-1}(s)$ is connected, and a relative group law for $f$ exists. Let $g : \mathbb{N}$ be such that every fibre $f^{-1}(s)$ has topological Krull dimension $g$, and let $n : \mathbb{N}$ with $(n : k) \neq 0$. Write $[n] = L.\mathtt{schemeNsmul}\ n : A \to A$ for the underlying morphism of the $n$-fold group-law multiple of the identity point $\mathrm{id}_A$. Then for any scheme $Z$ and any $g_1, g_2 : Z \to A$ with $g_1$ followed by $[n]$ equal to $g_2$ followed by $[n]$, there is a family of open subschemes $U_P \subseteq Z$ indexed by the $P$ in the group $L.\mathtt{AlgPoints}\ hc\ k$ of $k$-points of $A$ (the sections of $f$ over $\operatorname{Spec}$ of the identity algebra map, written additively) satisfying $n \cdot P = 0$, such that $\bigsqcup_P U_P = \top$ and, for every such $P$, the open immersion $U_P \hookrightarrow Z$ followed by $g_2$ equals $U_P \hookrightarrow Z$ followed by $g_1$ followed by the translation $\mathtt{translation}\ f\ L\ P$, namely the group-law product of the identity point of $A$ with the constant point $f$ followed by $P$. No disjointness, openness-and-closedness, or injectivity of the indexing family is asserted.
--
--   This is the scheme-theoretic statement that the fibre product $A \times_{[n], A, [n]} A$ decomposes, for $n$ invertible in $k$, into the graphs of the translations by the $n$-torsion $k$-points: any two morphisms into $A$ that become equal after composing with $[n]$ agree up to such a translation, locally on the source. It rests on $[n]$ being finite, flat and étale in this situation, together with the splitting of finite étale schemes over an algebraically closed field, and is used in the construction of descent data and of isomorphisms between pullbacks along $[n]$ in the Riemann form development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_iSup_eq_top_iota_comp_eq_iota_comp_comp_translation_of_comp_schemeNsmul_eq.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RiemannForm
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RiemannForm

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.exists_iSup_eq_top_iota_comp_eq_iota_comp_comp_translation_of_comp_schemeNsmul_eq
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (g : ℕ) (hdim : ∀ s : ↥(Spec (CommRingCat.of k)), topologicalKrullDim ↥(f.base ⁻¹' {s}) = g)
    (n : ℕ) (hn : (n : k) ≠ 0)
    {Z : Scheme.{0}} (g₁ g₂ : Z ⟶ A) (h : g₁ ≫ L.schemeNsmul n = g₂ ≫ L.schemeNsmul n) :
    ∃ U : {P : L.AlgPoints hc k // n • P = 0} → Z.Opens, ⨆ P, U P = ⊤ ∧
      ∀ P, (U P).ι ≫ g₂ = (U P).ι ≫ g₁ ≫ translation f L (RelativeGroupLaw.AlgPoints.toPoint P.1) := by sorry
