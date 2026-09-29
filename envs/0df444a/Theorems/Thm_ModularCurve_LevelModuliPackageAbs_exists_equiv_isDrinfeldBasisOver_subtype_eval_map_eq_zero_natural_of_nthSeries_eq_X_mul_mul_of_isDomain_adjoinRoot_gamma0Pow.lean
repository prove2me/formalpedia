-- Prove2me | Theorems.Thm_ModularCurve_LevelModuliPackageAbs_exists_equiv_isDrinfeldBasisOver_subtype_eval_map_eq_zero_natural_of_nthSeries_eq_X_mul_mul_of_isDomain_adjoinRoot_gamma0Pow
-- name    : ModularCurve.LevelModuliPackageAbs.exists_equiv_isDrinfeldBasisOver_subtype_eval_map_eq_zero_natural_of_nthSeries_eq_X_mul_mul_of_isDomain_adjoinRoot_gamma0Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/28a8e141-0340-505d-b70c-b5ea60b53dd4
-- title:
--   Drinfeld partners of a q-torsion point are roots of the Igusa factor
-- statement:
--   Throughout, $q$ and $\ell$ are primes with $3\le\ell$, $M'$ a nonzero natural number, and $A_0$ a commutative ring.
--
--   **Level-data coherence.** The hypotheses `hℓ` and `hM` state, for every $A_0$-algebra $T$, every Weierstrass curve $W$ over $T$ and every variable change $C$, that [`ModularCurve.IsLevelPStructure W ℓ D`](def/ModularCurve_KatzLevelP.html#L104) is carried by $C$ to `IsLevelPStructure (C • W) ℓ (D.variableChange C)`, and that [`ModularCurve.IsGamma0PowAt W p k h`](def/ModularCurve_WeierstrassGamma0Pow.html#L55) is carried to `IsGamma0PowAt (C • W) p k (kernelVariableChangeDeg C (gamma0PowDeg p k) h)`; `hℓ'` and `hM'` are the same two statements for $W_0$-algebras. Here a level-$\ell$ structure is a quadruple $(x_P,y_P,x_Q,y_Q)$ of affine points on $W$ annihilated by $W.\mathrm{pre}\Psi_\ell$ with both independence elements `indepElt` units, and `IsGamma0PowAt W p k h` asks that $h$ be a two-torsion kernel generator when $p^k=2$ and otherwise a cyclic $p^k$-kernel generator in the sense of `IsCyclicGenKernel`.
--
--   **Group-law data.** $\mathcal G$ is a family `GroupLaws A₀` assigning to each $A_0$-algebra $T$, each projective Weierstrass model $W$ over $T$ and each proof that $\Delta_W$ is a unit a relative group law on `projModelStrCR W`; `h𝒢` says each such law admits a points-evaluation (chord–tangent addition), and `h𝒢O` that its unit section is cut out in the origin chart by a ring homomorphism killing $x/y$ and $z/y$. $\mathcal T$ is a `LevelTransport A₀ 𝒢 q`, i.e. functorial transport of raw Drinfeld pairs along algebra maps and variable changes preserving `RawDrinfeldPair.IsLevel`, and `h𝒯` is the compatibility of the transported sections with the geometric pullbacks along `Proj.map` of coefficient and variable-change homomorphisms. The hypotheses `h𝒢r`, `h𝒢Or` are the chord–tangent and origin-identity properties of $\mathcal G$ restricted to scalars over $W_0$.
--
--   **Moduli packages.** $P_0$ is a `LevelModuliPackageAbs` over $A_0$ for the moduli datum of `rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯`, the rigid datum whose raw points over $T$ are a Weierstrass curve with unit discriminant together with a $\Gamma_0$-tuple of polynomials indexed by the prime factors of $M'$, a level-$\ell$ datum and a raw Drinfeld pair, all satisfying the corresponding `IsLevel` predicates, points being the quotient by variable changes; thus $P_0.B_0$ carries a universal point $P_0.\mathrm{univ}$ through which every point over every $A_0$-algebra factors uniquely. Similarly $P_{et}$ is a package over $W_0$ for the product of the $\Gamma_0(M')$-component, the level-$\ell$ component and the trivial component (no Drinfeld level), $x_{et}$ is a raw point over $P_{et}.B_0$ and `hxet` asserts that its class is $P_{et}.\mathrm{univ}$.
--
--   **Rings of coefficients and deformation rings.** $R$ is a noetherian local ring, complete for its maximal-ideal topology, an $A_0$-algebra, with $\iota : P_0.B_0 \to R$ an $A_0$-algebra map; $k$ is a field of characteristic $q$ in which $\ell$ and $M'$ are nonzero; $\mathrm{res}_R : R \to k$ is surjective with kernel the maximal ideal. $W_0$ is a complete discrete valuation domain with maximal ideal $(q)$ and a surjection $\mathrm{res}_0 : W_0 \to k$ with kernel the maximal ideal; $R$ is a $W_0$-algebra and $W_0$ an $A_0$-algebra in a scalar tower, with `hresR₀` the compatibility $\mathrm{res}_R\circ\mathrm{alg} = \mathrm{res}_0$. The hypothesis `hfac` is the universal property of $(R,\iota)$: for every Artinian local $W_0$- and $A_0$-algebra $T$ in the tower, with a surjection $\mathrm{res}_T : T \to k$ of kernel the maximal ideal lying over $\mathrm{res}_0$, every $A_0$-algebra map $\varphi : P_0.B_0 \to T$ with $\mathrm{res}_T\circ\varphi = \mathrm{res}_R\circ\iota$ extends through a unique $W_0$-algebra map $R \to T$ compatible with the residue maps and with $\iota$.
--
--   **The universal $q$-torsion point.** $CQ$ is a $P_{et}.B_0$- and $W_0$-algebra in a tower, and $Q_u$ is a section of the projective model of $x_{et}.\mathrm{curve}$ over $\operatorname{Spec} CQ$ with $q\,Q_u$ the unit section (`hQu`); `hrep` states that $CQ$ represents the $q$-torsion: for every $P_{et}.B_0$-algebra $T$ and every section $Q$ over $\operatorname{Spec} T$, one has $q\,Q =$ unit section if and only if there is a unique $P_{et}.B_0$-algebra map $\chi : CQ \to T$ with $\operatorname{Spec}\chi$ followed by $Q_u$ equal to $Q$.
--
--   **The torsion-lift ring and the Igusa factorisation.** $S$ is a noetherian local ring, complete for its maximal ideal, a $W_0$-algebra, with $\iota_S : CQ \to S$ a $W_0$-algebra map, a surjection $\mathrm{res}_S : S \to k$ of kernel the maximal ideal lying over $\mathrm{res}_0$, and `hfacS` the corresponding universal property of $(S,\iota_S)$ among Artinian local $W_0$-algebras with residue map to $k$ over $\mathrm{res}_0$. $F_S$ is a formal group over $S$ whose power series is the formal group law `formalGroupLawFixed` of $x_{et}.\mathrm{curve}$ base-changed along $\iota_S\circ(\text{alg. map } P_{et}.B_0\to CQ)$. Further, $g \in S[X]$ is monic of degree $q-1$, all coefficients below degree $q-1$ lie in the maximal ideal, the constant coefficient is $q$ times a unit, $v$ is a unit power series, and `hfacq` is the factorisation of the $q$-th iterate series $F_S.\mathrm{nthSeries}\,q = X\cdot g\cdot v$. Two further hypotheses are imposed: `AdjoinRoot g`, that is $S[X]/(g)$, is a domain, and $q \neq 0$ in $S$.
--
--   **Reduction data over $k$.** The field $k$ is an $A_0$-, $W_0$- and $P_{et}.B_0$-algebra with the tower over $A_0$, the structure map from $W_0$ being $\mathrm{res}_0$ (`hk₀`); $\rho : P_0.B_0 \to k$ satisfies $\rho = \mathrm{res}_R\circ\iota$ pointwise; $\psi_{et} : P_{et}.B_0 \to k$ satisfies $\psi_{et}(b) = \mathrm{res}_S(\iota_S(b))$ pointwise and coincides with the structure map of $k$ over $P_{et}.B_0$; the base change of $x_{et}.\mathrm{curve}$ along $\psi_{et}$ has unit discriminant ($h\Delta_k$); $Q_k$ is a section of that curve over $k$. The hypothesis `hQk_pin` pins $Q_k$ as the reduction of $Q_u$: there are a graded ring homomorphism $\varphi$ from the grading of the projective model of $x_{et}.\mathrm{curve}$ to that of its base change along $\psi_{et}$, and a containment $h\varphi$ of the irrelevant ideal of the target in the image of the irrelevant ideal of the source, such that $\varphi$ is a coefficient homomorphism for $\psi_{et}$ (it acts as $\psi_{et}$ on constants and fixes the three coordinates) and $Q_k$ followed by `Proj.map φ hφ` equals $\operatorname{Spec}(\mathrm{res}_S\circ\iota_S)$ followed by $Q_u$. Moreover $Q_k$ is not the unit section (`hQk`); for each prime factor $p$ of $M'$ the reduction of the $\Gamma_0$-polynomial $x_{et}.\mathrm{level}$ at $p$ is a $\Gamma_0(p^{v_p(M')})$-kernel generator for the reduced curve (`hhk`); the reduction of the level-$\ell$ datum is a level-$\ell$ structure (`hDk`); the raw Drinfeld pair consisting of the reduced curve, the unit section as first member and $Q_k$ as second member satisfies `RawDrinfeldPair.IsLevel 𝒢 q`, i.e. is a Drinfeld $\Gamma(q)$-basis of the reduced curve (`hyk`); and `hρyk` states that the image of $P_0.\mathrm{univ}$ under $\rho$ is the class of exactly this raw datum over $k$, assembled from the reduced curve, the reduced $\Gamma_0$- and level-$\ell$ data and that pair.
--
--   **Conclusion.** There is a family $\gamma$, indexed by every Artinian local $W_0$-algebra $T$ with surjection $\mathrm{res}_T : T\to k$ of kernel the maximal ideal lying over $\mathrm{res}_0$, every $W_0$-algebra map $\Phi : S \to T$, every $\psi : P_{et}.B_0 \to T$ with $\psi(b) = \Phi(\iota_S(b))$ pointwise, and every morphism $Q_m : \operatorname{Spec} T \to \operatorname{Proj}$ of the model of $x_{et}.\mathrm{curve}$ equal to $\operatorname{Spec}(\Phi\circ\iota_S)$ followed by $Q_u$, of bijections
--   $$\gamma : \{P_m\} \;\simeq\; \{\pi \in T : (g^{\Phi})(\pi) = 0\},$$
--   where the left-hand set consists of those $P_m : \operatorname{Spec} T \to \operatorname{Proj}$ for which, first, there are factorisations $hP$ of $P_m$ and $hQ$ of $Q_m$ through the structure morphism equal to $\operatorname{Spec}\psi$, such that the resulting pair $(\langle P_m,hP\rangle,\langle Q_m,hQ\rangle)$ of sections over $\operatorname{Spec}\psi$ is a relative Drinfeld basis for the group law $\mathcal G$ restricted to $W_0$ at $P_{et}.B_0$ and $x_{et}.\mathrm{curve}$, that is, the basis divisor `basisDivisorOver` of the pair equals the $q$-torsion ideal sheaf data `torsionIdealOver` over that base; and second, $\operatorname{Spec}(\mathrm{res}_T)$ followed by $P_m$ is the unit section of that group law over $\operatorname{Spec}\psi_{et}$, so that $P_m$ reduces to the origin modulo the maximal ideal of $T$. On the right, $g^\Phi = g.\mathrm{map}\,\Phi$ is the image of the Igusa factor in $T[X]$.
--
--   The family is natural in the test algebra: for all $T$, $T'$ as above with residue maps $\mathrm{res}_T$, $\mathrm{res}_{T'}$, every $W_0$-algebra map $f : T \to T'$ with $\mathrm{res}_{T'}\circ f = \mathrm{res}_T$, every $\Phi$, $\psi$, $Q_m$ over $T$ as above and the corresponding data $\psi'$, $Q_m'$ over $T'$ attached to $f\circ\Phi$, and all $P$ in the left-hand set over $T$ and $P'$ in the left-hand set over $T'$, if $P' = \operatorname{Spec} f$ followed by $P$, then the parameter attached to $P'$ over $T'$ is $f$ applied to the parameter attached to $P$ over $T$.
--
--   This is the deformation-theoretic description of the Drinfeld $\Gamma(q)$-partners, at the ordinary point, of the universal $q$-torsion point: over any Artinian local test algebra the partners reducing to the origin are in natural bijection with the roots of the Igusa factor $g$ of the $q$-division series of the formal group, the bijection being compatible with base change. It is used by [`ModularCurve.LevelModuliPackageAbs.exists_algHom_equiv_subtype_eval_map_eq_zero_natural_of_factorsThrough_of_nthSeries_eq_X_mul_mul_of_isDomain_adjoinRoot_gamma0Pow`](thm.html#ModularCurve.LevelModuliPackageAbs.exists_algHom_equiv_subtype_eval_map_eq_zero_natural_of_factorsThrough_of_nthSeries_eq_X_mul_mul_of_isDomain_adjoinRoot_gamma0Pow) to identify the deformation ring of the Drinfeld level structure with a ring of the form $S[X]/(g)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_LevelModuliPackageAbs_exists_equiv_isDrinfeldBasisOver_subtype_eval_map_eq_zero_natural_of_nthSeries_eq_X_mul_mul_of_isDomain_adjoinRoot_gamma0Pow.lean

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctorRestrict
import Definitions.Def_WeierstrassCurve_DrinfeldBasisRelative
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel IsLocalRing FormalGroup
  AlgebraicGeometry CategoryTheory NeronModelInfra Polynomial

attribute [local instance] MvPolynomial.gradedAlgebra

theorem ModularCurve.LevelModuliPackageAbs.exists_equiv_isDrinfeldBasisOver_subtype_eval_map_eq_zero_natural_of_nthSeries_eq_X_mul_mul_of_isDomain_adjoinRoot_gamma0Pow
    (q : ℕ) [Fact q.Prime] (ℓ M' : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) [NeZero M']
    (A₀ : Type) [CommRing A₀]

    (hℓ : ∀ (T : Type) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsLevelPStructure W ℓ D →
        ModularCurve.IsLevelPStructure (C • W) ℓ (D.variableChange C))
    (hM : ∀ (T : Type) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (𝒢 : GroupLaws A₀) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (𝒯 : LevelTransport A₀ 𝒢 q) (h𝒯 : 𝒯.IsSectionTransport)
    (P₀ : LevelModuliPackageAbs A₀ (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum)
    (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R]
    [Algebra A₀ R] (ι : P₀.B₀ →ₐ[A₀] R)
    (k : Type) [Field k] [CharP k q] (hℓk : ((ℓ : ℕ) : k) ≠ 0) (hM'k : ((M' : ℕ) : k) ≠ 0)
    (resR : R →+* k) (hresR : Function.Surjective resR) (hkerR : RingHom.ker resR = maximalIdeal R)
    (W₀ : Type) [CommRing W₀] [IsDomain W₀] [IsDiscreteValuationRing W₀]
    [IsAdicComplete (maximalIdeal W₀) W₀] (hW₀ : maximalIdeal W₀ = Ideal.span {(q : W₀)})
    (res₀ : W₀ →+* k) (hres₀ : Function.Surjective res₀) (hker₀ : RingHom.ker res₀ = maximalIdeal W₀)
    [Algebra W₀ R] [Algebra A₀ W₀] [IsScalarTower A₀ W₀ R]
    (hresR₀ : ∀ w : W₀, resR (algebraMap W₀ R w) = res₀ w)
    (hfac : ∀ (T : Type) [CommRing T] [IsLocalRing T] [IsArtinianRing T] [Algebra W₀ T]
        [Algebra A₀ T] [IsScalarTower A₀ W₀ T]
        (resT : T →+* k), Function.Surjective resT → RingHom.ker resT = maximalIdeal T →
        (∀ w : W₀, resT (algebraMap W₀ T w) = res₀ w) →
        ∀ φ : P₀.B₀ →ₐ[A₀] T, (∀ b : P₀.B₀, resT (φ b) = resR (ι b)) →
          ∃! Φ : R →ₐ[W₀] T, (∀ r : R, resT (Φ r) = resR r) ∧ ∀ b : P₀.B₀, Φ (ι b) = φ b)

    (hℓ' : ∀ (T : Type) [CommRing T] [Algebra W₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsLevelPStructure W ℓ D →
        ModularCurve.IsLevelPStructure (C • W) ℓ (D.variableChange C))
    (hM' : ∀ (T : Type) [CommRing T] [Algebra W₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))

    (h𝒢r : (𝒢.restrictScalars W₀).IsChordTangent) (h𝒢Or : (𝒢.restrictScalars W₀).IsOriginIdentity)
    (Pet : LevelModuliPackageAbs W₀
      (((ModularCurve.gamma0PowComponent W₀ M' hM').prod
        ((ModularCurve.levelPComponent W₀ ℓ hℓ').prod (ModularCurve.LevelComponent.trivial (A := W₀)))).toRigid).toLevelModuliDatum)
    (xet : (((ModularCurve.gamma0PowComponent W₀ M' hM').prod
        ((ModularCurve.levelPComponent W₀ ℓ hℓ').prod (ModularCurve.LevelComponent.trivial (A := W₀)))).toRigid).Raw Pet.B₀)
    (hxet : (Quot.mk _ xet :
      (((ModularCurve.gamma0PowComponent W₀ M' hM').prod
        ((ModularCurve.levelPComponent W₀ ℓ hℓ').prod (ModularCurve.LevelComponent.trivial (A := W₀)))).toRigid).Pt Pet.B₀) =
        Pet.univ)
    (CQ : Type) [CommRing CQ] [Algebra Pet.B₀ CQ] [Algebra W₀ CQ] [IsScalarTower W₀ Pet.B₀ CQ]
    (Qu : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap Pet.B₀ CQ))) (projModelStrCR xet.curve))
    (hQu : ((𝒢.restrictScalars W₀) Pet.B₀ xet.curve xet.isUnit_Δ).nsmul _ q Qu =
      ((𝒢.restrictScalars W₀) Pet.B₀ xet.curve xet.isUnit_Δ).one _)
    (hrep : ∀ (T : Type) [CommRing T] [Algebra Pet.B₀ T]
        (Q : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap Pet.B₀ T))) (projModelStrCR xet.curve)),
        ((𝒢.restrictScalars W₀) Pet.B₀ xet.curve xet.isUnit_Δ).nsmul _ q Q =
            ((𝒢.restrictScalars W₀) Pet.B₀ xet.curve xet.isUnit_Δ).one _ ↔
          ∃! χ : CQ →ₐ[Pet.B₀] T, Spec.map (CommRingCat.ofHom χ.toRingHom) ≫ Qu.1 = Q.1)

    (S : Type) [CommRing S] [IsLocalRing S] [IsNoetherianRing S] [IsAdicComplete (maximalIdeal S) S]
    [Algebra W₀ S] (ιS : CQ →ₐ[W₀] S)
    (resS : S →+* k) (hresS : Function.Surjective resS) (hkerS : RingHom.ker resS = maximalIdeal S)
    (hresS₀ : ∀ w : W₀, resS (algebraMap W₀ S w) = res₀ w)
    (hfacS : ∀ (T : Type) [CommRing T] [IsLocalRing T] [IsArtinianRing T] [Algebra W₀ T]
        (resT : T →+* k), Function.Surjective resT → RingHom.ker resT = maximalIdeal T →
        (∀ w : W₀, resT (algebraMap W₀ T w) = res₀ w) →
        ∀ φ : CQ →ₐ[W₀] T, (∀ c : CQ, resT (φ c) = resS (ιS c)) →
          ∃! Φ : S →ₐ[W₀] T, (∀ s : S, resT (Φ s) = resS s) ∧ ∀ c : CQ, Φ (ιS c) = φ c)

    (FS : FormalGroup S)
    (hFS : FS.toPowerSeries = (xet.curve.map ((ιS : CQ →+* S).comp (algebraMap Pet.B₀ CQ))).formalGroupLawFixed)
    (g : S[X]) (v : PowerSeries S) (hgm : g.Monic) (hgdeg : g.natDegree = q - 1)
    (hgcoeff : ∀ i < q - 1, g.coeff i ∈ maximalIdeal S) (hg0 : ∃ w : S, IsUnit w ∧ g.coeff 0 = (q : S) * w)
    (hv : IsUnit v)
    (hfacq : FS.nthSeries q = PowerSeries.X * (↑g : PowerSeries S) * v)

    (hdom : IsDomain (AdjoinRoot g)) (hqS : (q : S) ≠ 0)

    [Algebra A₀ k] [Algebra W₀ k] [IsScalarTower A₀ W₀ k] [Algebra Pet.B₀ k]
    (hk₀ : ∀ w : W₀, algebraMap W₀ k w = res₀ w)
    (ρ : P₀.B₀ →ₐ[A₀] k) (hρ : ∀ b : P₀.B₀, ρ b = resR (ι b))
    (ψet : Pet.B₀ →ₐ[W₀] k) (hψet : ∀ b : Pet.B₀, ψet b = resS (ιS (algebraMap Pet.B₀ CQ b)))
    (hψalg : ∀ b : Pet.B₀, algebraMap Pet.B₀ k b = ψet b)
    (hΔk : IsUnit (xet.curve.map ψet.toRingHom).Δ)
    (Qk : Section (xet.curve.map ψet.toRingHom))
    (hQk_pin : ∃ (φ : projModelGradingCR xet.curve →+*ᵍ projModelGradingCR (xet.curve.map ψet.toRingHom))
        (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (xet.curve.map ψet.toRingHom)) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR xet.curve)).map φ),
        IsCoefficientHom xet.curve ψet.toRingHom φ ∧
          Qk.1 ≫ Proj.map φ hφ = Spec.map (CommRingCat.ofHom (resS.comp (ιS : CQ →+* S))) ≫ Qu.1)
    (hQk : Qk ≠ (𝒢 k (xet.curve.map ψet.toRingHom) hΔk).one (𝟙 (base (T := k))))

    (hhk : ∀ p : ↥M'.primeFactors, ModularCurve.IsGamma0PowAt (xet.curve.map ψet.toRingHom) (p : ℕ) (M'.factorization (p : ℕ))
      ((xet.level.1 p).map ψet.toRingHom))
    (hDk : ModularCurve.IsLevelPStructure (xet.curve.map ψet.toRingHom) ℓ (xet.level.2.1.map ψet.toRingHom))
    (hyk : RawDrinfeldPair.IsLevel 𝒢 q (xet.curve.map ψet.toRingHom)
      ⟨xet.curve.map ψet.toRingHom, (𝒢 k (xet.curve.map ψet.toRingHom) hΔk).one (𝟙 (base (T := k))), Qk⟩)
    (hρyk : (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.map ρ P₀.univ =
      (Quot.mk _ (⟨xet.curve.map ψet.toRingHom, hΔk,
          ⟨fun p => (xet.level.1 p).map ψet.toRingHom, xet.level.2.1.map ψet.toRingHom,
            ⟨xet.curve.map ψet.toRingHom, (𝒢 k (xet.curve.map ψet.toRingHom) hΔk).one (𝟙 (base (T := k))), Qk⟩⟩,
          ⟨hhk, hDk, hyk⟩⟩ : (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).Raw k) :
        (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).Pt k)) :
    ∃ γ : ∀ (T : Type) [CommRing T] [IsLocalRing T] [IsArtinianRing T] [Algebra W₀ T]
        (resT : T →+* k) (hT₁ : Function.Surjective resT) (hT₂ : RingHom.ker resT = maximalIdeal T)
        (hT₃ : ∀ w : W₀, resT (algebraMap W₀ T w) = res₀ w)
          (Φ : S →ₐ[W₀] T) (ψ : Pet.B₀ →ₐ[W₀] T) (_ : ∀ b : Pet.B₀, ψ b = Φ (ιS (algebraMap Pet.B₀ CQ b)))
          (Qm : base (T := T) ⟶ projModelCR xet.curve)
          (_ : Qm = Spec.map (CommRingCat.ofHom (Φ.toRingHom.comp (ιS : CQ →+* S))) ≫ Qu.1),
          {Pm : base (T := T) ⟶ projModelCR xet.curve //
              (∃ (hP : Pm ≫ projModelStrCR xet.curve = Spec.map (CommRingCat.ofHom (ψ).toRingHom))
                 (hQ : Qm ≫ projModelStrCR xet.curve = Spec.map (CommRingCat.ofHom (ψ).toRingHom)),
                 ((𝒢.restrictScalars W₀) Pet.B₀ xet.curve xet.isUnit_Δ).IsDrinfeldBasisOver q
                   (Spec.map (CommRingCat.ofHom (ψ).toRingHom)) ⟨Pm, hP⟩ ⟨Qm, hQ⟩) ∧
              Spec.map (CommRingCat.ofHom resT) ≫ Pm =
                (((𝒢.restrictScalars W₀) Pet.B₀ xet.curve xet.isUnit_Δ).one (Spec.map (CommRingCat.ofHom ψet.toRingHom))).1} ≃
            {π : T // (g.map (Φ : S →+* T)).eval π = 0},
      ∀ (T : Type) [CommRing T] [IsLocalRing T] [IsArtinianRing T] [Algebra W₀ T]
        (resT : T →+* k) (hT₁ : Function.Surjective resT) (hT₂ : RingHom.ker resT = maximalIdeal T)
        (hT₃ : ∀ w : W₀, resT (algebraMap W₀ T w) = res₀ w)
        (T' : Type) [CommRing T'] [IsLocalRing T'] [IsArtinianRing T'] [Algebra W₀ T']
        (resT' : T' →+* k) (hT'₁ : Function.Surjective resT') (hT'₂ : RingHom.ker resT' = maximalIdeal T')
        (hT'₃ : ∀ w : W₀, resT' (algebraMap W₀ T' w) = res₀ w)
        (f : T →ₐ[W₀] T') (_ : ∀ t : T, resT' (f t) = resT t)
        (Φ : S →ₐ[W₀] T) (ψ : Pet.B₀ →ₐ[W₀] T) (hψ : ∀ b : Pet.B₀, ψ b = Φ (ιS (algebraMap Pet.B₀ CQ b)))
        (Qm : base (T := T) ⟶ projModelCR xet.curve)
        (hQm : Qm = Spec.map (CommRingCat.ofHom (Φ.toRingHom.comp (ιS : CQ →+* S))) ≫ Qu.1)
        (ψ' : Pet.B₀ →ₐ[W₀] T') (hψ' : ∀ b : Pet.B₀, ψ' b = (f.comp Φ) (ιS (algebraMap Pet.B₀ CQ b)))
        (Qm' : base (T := T') ⟶ projModelCR xet.curve)
        (hQm' : Qm' = Spec.map (CommRingCat.ofHom ((f.comp Φ).toRingHom.comp (ιS : CQ →+* S))) ≫ Qu.1)
        (P : {Pm : base (T := T) ⟶ projModelCR xet.curve //
              (∃ (hP : Pm ≫ projModelStrCR xet.curve = Spec.map (CommRingCat.ofHom (ψ).toRingHom))
                 (hQ : Qm ≫ projModelStrCR xet.curve = Spec.map (CommRingCat.ofHom (ψ).toRingHom)),
                 ((𝒢.restrictScalars W₀) Pet.B₀ xet.curve xet.isUnit_Δ).IsDrinfeldBasisOver q
                   (Spec.map (CommRingCat.ofHom (ψ).toRingHom)) ⟨Pm, hP⟩ ⟨Qm, hQ⟩) ∧
              Spec.map (CommRingCat.ofHom resT) ≫ Pm =
                (((𝒢.restrictScalars W₀) Pet.B₀ xet.curve xet.isUnit_Δ).one (Spec.map (CommRingCat.ofHom ψet.toRingHom))).1})
        (P' : {Pm : base (T := T') ⟶ projModelCR xet.curve //
              (∃ (hP : Pm ≫ projModelStrCR xet.curve = Spec.map (CommRingCat.ofHom (ψ').toRingHom))
                 (hQ : Qm' ≫ projModelStrCR xet.curve = Spec.map (CommRingCat.ofHom (ψ').toRingHom)),
                 ((𝒢.restrictScalars W₀) Pet.B₀ xet.curve xet.isUnit_Δ).IsDrinfeldBasisOver q
                   (Spec.map (CommRingCat.ofHom (ψ').toRingHom)) ⟨Pm, hP⟩ ⟨Qm', hQ⟩) ∧
              Spec.map (CommRingCat.ofHom resT') ≫ Pm =
                (((𝒢.restrictScalars W₀) Pet.B₀ xet.curve xet.isUnit_Δ).one (Spec.map (CommRingCat.ofHom ψet.toRingHom))).1}),
        P'.1 = Spec.map (CommRingCat.ofHom f.toRingHom) ≫ P.1 →
          (γ T' resT' hT'₁ hT'₂ hT'₃ (f.comp Φ) ψ' hψ' Qm' hQm' P').1 =
            f ((γ T resT hT₁ hT₂ hT₃ Φ ψ hψ Qm hQm P).1) := by sorry
