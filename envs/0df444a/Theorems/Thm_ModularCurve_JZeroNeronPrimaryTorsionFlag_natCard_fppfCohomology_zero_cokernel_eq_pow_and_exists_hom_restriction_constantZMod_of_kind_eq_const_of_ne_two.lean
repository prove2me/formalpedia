-- Prove2me | Theorems.Thm_ModularCurve_JZeroNeronPrimaryTorsionFlag_natCard_fppfCohomology_zero_cokernel_eq_pow_and_exists_hom_restriction_constantZMod_of_kind_eq_const_of_ne_two
-- name    : ModularCurve.JZeroNeronPrimaryTorsionFlag.natCard_fppfCohomology_zero_cokernel_eq_pow_and_exists_hom_restriction_constantZMod_of_kind_eq_const_of_ne_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/9bf22aa1-803a-5df0-a552-1558605caf6a
-- title:
--   Constant-kind layer: H⁰ count and H¹ injection into ℤ/q
-- statement:
--   Let $p$ and $q$ be primes with $q \neq 2$, let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ lying over $p$ in the sense that $p$ belongs to the non-units of $A$, let $C$ be a core datum `JZeroNeronPrimaryTorsionCore p q A hA`, let $m$ be a natural number and let `flag` be a flag `JZeroNeronPrimaryTorsionFlag p q A hA C m`, consisting of the Hopf-algebra quotients $G_j$ of $C.H\,m$, the corresponding chain of abelian sheaves $F_j$ on the small fppf site of $\mathrm{Spec}\,\mathbb{Z}$ mapping to $C.\mathcal{J}\,m$, and the increasing Galois-stable chain `genericStep` of subgroups of `JZero p` from $\bot$ to `eisensteinPrimaryTorsionBar p q m`. Fix a step $i <$ `flag.n` whose layer kind `flag.kind i` is `const` (one of the two values of `JZeroFlagLayerKind`). Let $L$ be an abelian sheaf on that site and $pr : F_{i+1} \to L$ a morphism with $\mathrm{incl}_i$ followed by $pr$ zero, such that $0 \to F_i \to F_{i+1} \to L \to 0$ is short exact. Let $dt$ be a natural number such that the toric part at step $i+1$ exceeds that at step $i$ by the factor $q^{dt}$, that is
--   $$\#\bigl(\mathrm{jZeroToricTorsion}\,p\,A\,(q^m) \cap \mathrm{genericStep}(i+1)\bigr) = q^{dt}\cdot \#\bigl(\mathrm{jZeroToricTorsion}\,p\,A\,(q^m) \cap \mathrm{genericStep}(i)\bigr),$$
--   where `jZeroToricTorsion p A (q ^ m)` is the intersection of the $q^m$-torsion of `JZero p` with the image of the inertia-invariant points attached to $A$ under multiplication by `eisensteinNumerator p`. Then the group of global sections $H^0$ of $L$ on the small fppf site of $\mathrm{Spec}\,\mathbb{Z}$ has exactly $q^{dt}$ elements, and there exist an abelian sheaf $K$ on that site whose underlying presheaf is isomorphic to the restriction, along the forgetful functor from the small fppf site to schemes over $\mathrm{Spec}\,\mathbb{Z}$ and then to schemes, of the universe-lifted constant sheaf $\mathbb{Z}/q$, together with a morphism $f : L \to K$ whose induced map on fppf $H^1$ is injective.
--
--   This is the constant-kind case of the step-by-step analysis of a Jordan–Hölder flag of the Eisenstein-primary torsion sheaf of $J_0(p)$ over $\mathrm{Spec}\,\mathbb{Z}$, in the style of Mazur's study of the Eisenstein ideal: a layer of constant kind has precisely as many global fppf sections as the toric jump predicts, and its $H^1$ embeds into that of a model of the constant sheaf $\mathbb{Z}/q$. It is used by [`ModularCurve.JZeroNeronPrimaryTorsionFlag.exists_cokernel_h1_add_dt_le_h0_of_kind_eq_const_of_ne_two`](thm.html#ModularCurve.JZeroNeronPrimaryTorsionFlag.exists_cokernel_h1_add_dt_le_h0_of_kind_eq_const_of_ne_two), where the two conclusions are combined into a cohomological inequality for the layer.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZeroNeronPrimaryTorsionFlag_natCard_fppfCohomology_zero_cokernel_eq_pow_and_exists_hom_restriction_constantZMod_of_kind_eq_const_of_ne_two.lean

import Definitions.Def_ModularCurve_JZeroNeronPrimaryTorsionFlag

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicGeometry AlgebraicGeometry.Scheme ValuationSubring CategoryTheory

theorem ModularCurve.JZeroNeronPrimaryTorsionFlag.natCard_fppfCohomology_zero_cokernel_eq_pow_and_exists_hom_restriction_constantZMod_of_kind_eq_const_of_ne_two
    (p : ℕ) [Fact p.Prime] (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (C : JZeroNeronPrimaryTorsionCore p q A hA) (m : ℕ)
    (flag : JZeroNeronPrimaryTorsionFlag p q A hA C m) (i : Fin flag.n)
    (hk : flag.kind i = JZeroFlagLayerKind.const)
    (L : Sheaf (smallFppfTopology specInt) Ab.{1})
    (pr : flag.F i.succ ⟶ L) (hzero : flag.incl i ≫ pr = 0)
    (hses : (ShortComplex.mk (flag.incl i) pr hzero).ShortExact)
    (dt : ℕ)
    (ht : Nat.card ↥(jZeroToricTorsion p A (q ^ m) ⊓ flag.genericStep i.succ)
        = q ^ dt * Nat.card ↥(jZeroToricTorsion p A (q ^ m) ⊓ flag.genericStep i.castSucc)) :
    Nat.card (fppfCohomology specInt L 0) = q ^ dt ∧
    ∃ (K : Sheaf (smallFppfTopology specInt) Ab.{1})
      (_ : K.obj ≅ (Scheme.Fppf.forget specInt ⋙ Over.forget specInt).op ⋙
          (FppfKummerSES.sheafULift.{0}.obj
            (FppfRepresentableGroupSchemeSheaf.constantZModSheaf.{0} q)).obj)
      (f : L ⟶ K), Function.Injective (fppfCohomologyMap specInt f 1) := by sorry
