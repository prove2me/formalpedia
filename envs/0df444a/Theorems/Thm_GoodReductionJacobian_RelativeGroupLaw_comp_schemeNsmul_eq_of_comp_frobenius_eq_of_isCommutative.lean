-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_comp_schemeNsmul_eq_of_comp_frobenius_eq_of_isCommutative
-- name    : GoodReductionJacobian.RelativeGroupLaw.comp_schemeNsmul_eq_of_comp_frobenius_eq_of_isCommutative
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/f95d9491-0b7a-5ad3-8c33-e71cbbd8ac3e
-- title:
--   Multiplication by p coequalises the kernel pair of Frobenius
-- statement:
--   Let $p$ be a prime, let $X$ be a scheme with a morphism $f \colon X \to \operatorname{Spec}\mathbb{Z}/p$ that is locally of finite type, and let $L$ be a relative group law on $f$ over $\mathbb{Z}/p$: that is, a functorial group structure on the sets $\{\varphi \colon T \to X \mid \varphi \circ f = t\}$ of $X$-points over each $t \colon T \to \operatorname{Spec}\mathbb{Z}/p$, with multiplication, unit and inverse satisfying associativity, the unit laws, left inverse cancellation, and compatibility with base change along any $\psi \colon T' \to T$ over $\operatorname{Spec}\mathbb{Z}/p$. Assume $L$ is commutative, i.e. its multiplication on each point set is commutative. Let $F \colon X \to X$ be a morphism with $F \circ f = f$ subject to the hypothesis that for every commutative $\mathbb{Z}/p$-algebra $B$ of characteristic $p$ and every morphism $x \colon \operatorname{Spec} B \to X$ over $\operatorname{Spec}\mathbb{Z}/p$ one has $x$ followed by $F$ equal to $\operatorname{Spec}$ of the Frobenius $b \mapsto b^{p}$ of $B$ followed by $x$. Write $[p] \colon X \to X$ for `L.schemeNsmul p`, the underlying morphism of the $p$-fold $L$-product of the identity point $\mathrm{id}_X$ with itself. Then for any scheme $Z$ and any $g_1, g_2 \colon Z \to X$ with $g_1$ followed by $F$ equal to $g_2$ followed by $F$, also $g_1$ followed by $[p]$ equals $g_2$ followed by $[p]$.
--
--   The statement expresses the inclusion $\ker F \subseteq \ker [p]$ for a commutative group law in characteristic $p$, in the form of the coequalising condition needed to factor multiplication by $p$ through the relative Frobenius. It is used in the construction of the Verschiebung, namely in [`ModularCurve.JHNeronObjectAtP.LevelData.exists_verschiebung_comp_frobenius_eq_schemeNsmul`](thm.html#ModularCurve.JHNeronObjectAtP.LevelData.exists_verschiebung_comp_frobenius_eq_schemeNsmul), where a morphism $V$ with $F$ followed by $V$ equal to $[p]$ is produced.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_comp_schemeNsmul_eq_of_comp_frobenius_eq_of_isCommutative.lean

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.comp_schemeNsmul_eq_of_comp_frobenius_eq_of_isCommutative
    (p : ℕ) [Fact p.Prime] {X : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of (ZMod p))} [LocallyOfFiniteType f]
    (L : RelativeGroupLaw (ZMod p) f) (hc : L.IsCommutative)
    (F : SchemeHomOver f f)
    (hF : ∀ (B : Type) [CommRing B] [Algebra (ZMod p) B] [CharP B p]
      (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) B))) f),
      (NeronModelInfra.schemeHomOverComp x F).1 = Spec.map (CommRingCat.ofHom (frobenius B p)) ≫ x.1)
    {Z : Scheme.{0}} (g₁ g₂ : Z ⟶ X) (h : g₁ ≫ F.1 = g₂ ≫ F.1) :
    g₁ ≫ L.schemeNsmul p = g₂ ≫ L.schemeNsmul p := by sorry
