-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackage_forall_exists_orientedCrossingChart
-- name    : ModularCurve.DRModelPackage.forall_exists_orientedCrossingChart
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.564058+00:00
-- url     : https://prove2.me/theorems/70246751-dc3d-58db-9eab-b51cc7a8252a
-- title:
--   Oriented crossing charts for the Deligne–Rapoport model at p
-- statement:
--   Fix a prime $p$ with $5 \le p$ and a term $\mathfrak{X}$ of `DRModelPackage p`, the structure bundling the properness, flatness, integrality and normality of the two-chart integral model `DRModel p` over $\operatorname{Spec}\mathbb{Z}$ together with its rational and geometric curve models, its two sections over $\operatorname{Spec}\mathbb{Z}$, its smooth locus and the attached component data. Let $O$ be a discrete valuation domain whose maximal ideal is $(p)$, let $\kappa$ be an algebraically closed field of characteristic $p$, and let $\mathrm{to}\kappa : O \to \kappa$ be a ring homomorphism. Let $\mathrm{bc}$ be a morphism from the base change of `DRModel p` along $\mathbb{Z} \to \kappa$ to its base change $X$ along $\mathbb{Z} \to O$ that commutes with the first projections and satisfies $\mathrm{bc}$ followed by the second projection $=$ the second projection followed by $\operatorname{Spec}(\mathrm{to}\kappa)$. Points of the fibre product of the two component morphisms $\mathfrak{X}.\mathrm{compInf}\,\kappa$ and $\mathfrak{X}.\mathrm{compZero}\,\kappa$ play the role of crossing points; for such a point $n$ write $x_n$ for its image in $X$ under the first projection, $\mathfrak{X}.\mathrm{compInf}\,\kappa$ and $\mathrm{bc}$. It is assumed (hypothesis `hrat`) that every such $x_n$ is rational over the residue field of $O$: there is a morphism $s$ from $\operatorname{Spec}$ of the residue field of $O$ to $X$ lying over $\operatorname{Spec}$ of the residue map and sending the closed point to $x_n$. The conclusion asserts, for every crossing point $n$, the existence of an integer $e \ge 1$, an open subscheme $U$ of $X$ with $x_n \in U$, and a morphism $f : U \to \operatorname{Spec}\bigl(O[X_0,X_1]/(X_0X_1 - p^e)\bigr)$ such that: (i) $f$ followed by $\operatorname{Spec}$ of the structure map $O \to$ `CrossingQuotient O (p^e)` equals the open immersion $U \hookrightarrow X$ followed by the projection to $\operatorname{Spec} O$, so $f$ is a morphism of $O$-schemes; (ii) for $y \in U$, both distinguished elements `CrossingQuotient.U (p^e)` and `CrossingQuotient.V (p^e)` lie in the prime $f(y)$ exactly when $y$ maps to $x_n$, so the fibre over the singular point of the crossing scheme is the single point $x_n$; (iii) at every such $y$ the induced local homomorphism on stalks is flat, carries the maximal ideal of the source onto a set generating the maximal ideal of the target, and induces an isomorphism of residue fields; and (iv) the chart is oriented: for $y \in U$, `CrossingQuotient.V (p^e)` lies in $f(y)$ if and only if $y$ maps into the image of $\mathfrak{X}.\mathrm{compInf}\,\kappa$ followed by $\mathrm{bc}$, and `CrossingQuotient.U (p^e)` lies in $f(y)$ if and only if $y$ maps into the image of $\mathfrak{X}.\mathrm{compZero}\,\kappa$ followed by $\mathrm{bc}$ (each direction being a separate clause).
--
--   This is the formal counterpart of the Deligne–Rapoport local description of the modular curve at its supersingular crossings, where the completed local ring has the shape $W[[x,y]]/(xy-p^{e})$, here expressed as an étale-type chart to $\operatorname{Spec} O[u,v]/(uv-p^{e})$ with the branch $v=0$ matching the $\infty$-component and $u=0$ the $0$-component. It is used to assemble the resolved Deligne–Rapoport model together with its charts, and in the proof that the stalks of the base change of `DRModel p` to $O$ are integrally closed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackage_forall_exists_orientedCrossingChart.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackage
import Definitions.Def_MvPolynomial_CrossingResolutionScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial ModularCurve

theorem ModularCurve.DRModelPackage.forall_exists_orientedCrossingChart
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (𝔛 : DRModelPackage p)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] (toκ : O →+* κ)

    (bc : pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ))) ⟶
      pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))
    (hbc₁ : bc ≫ pullback.fst _ _ = pullback.fst _ _)
    (hbc₂ : bc ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom toκ))

    (hrat : ∀ x : ↥(pullback (𝔛.compInf κ) (𝔛.compZero κ)),
      ∃ s : Spec (CommRingCat.of (IsLocalRing.ResidueField O)) ⟶
          pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))),
        s ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)) ∧
        s.base (IsLocalRing.closedPoint (IsLocalRing.ResidueField O)) =
          (pullback.fst (𝔛.compInf κ) (𝔛.compZero κ) ≫ 𝔛.compInf κ ≫ bc).base x) :
    ∀ n : ↥(pullback (𝔛.compInf κ) (𝔛.compZero κ)),
      ∃ (e : ℕ) (_ : 1 ≤ e)
        (U : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).Opens)
        (_ : (pullback.fst (𝔛.compInf κ) (𝔛.compZero κ) ≫ 𝔛.compInf κ ≫ bc).base n ∈ U)
        (f : (U : Scheme.{0}) ⟶ CrossingQuotient.crossingScheme (((p : ℕ) : O) ^ e)),

        f ≫ Spec.map (CommRingCat.ofHom (algebraMap O (CrossingQuotient O (((p : ℕ) : O) ^ e)))) =
            U.ι ≫ pullback.snd _ _ ∧

        (∀ y : ↥(U : Scheme.{0}),
            (CrossingQuotient.U (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal ∧
              CrossingQuotient.V (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal) ↔
            U.ι.base y = (pullback.fst (𝔛.compInf κ) (𝔛.compZero κ) ≫ 𝔛.compInf κ ≫ bc).base n) ∧

        (∀ y : ↥(U : Scheme.{0}), U.ι.base y = (pullback.fst (𝔛.compInf κ) (𝔛.compZero κ) ≫ 𝔛.compInf κ ≫ bc).base n →
            (f.stalkMap y).hom.Flat ∧
            Ideal.map (f.stalkMap y).hom (IsLocalRing.maximalIdeal _) = IsLocalRing.maximalIdeal _ ∧
            IsIso (f.residueFieldMap y)) ∧

        (∀ y : ↥(U : Scheme.{0}), CrossingQuotient.V (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal →
            U.ι.base y ∈ Set.range (𝔛.compInf κ ≫ bc).base) ∧
        (∀ y : ↥(U : Scheme.{0}), CrossingQuotient.U (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal →
            U.ι.base y ∈ Set.range (𝔛.compZero κ ≫ bc).base) ∧

        (∀ y : ↥(U : Scheme.{0}), U.ι.base y ∈ Set.range (𝔛.compInf κ ≫ bc).base →
            CrossingQuotient.V (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal) ∧
        (∀ y : ↥(U : Scheme.{0}), U.ι.base y ∈ Set.range (𝔛.compZero κ ≫ bc).base →
            CrossingQuotient.U (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal) := by sorry
