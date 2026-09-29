-- Prove2me | Theorems.Thm_ModularCurve_LevelModuliPackageAbs_exists_algHom_equiv_subtype_eval_map_eq_zero_natural_of_factorsThrough_of_nthSeries_eq_X_mul_mul_of_isDomain_adjoinRoot_rigidDataH1Pow
-- name    : ModularCurve.LevelModuliPackageAbs.exists_algHom_equiv_subtype_eval_map_eq_zero_natural_of_factorsThrough_of_nthSeries_eq_X_mul_mul_of_isDomain_adjoinRoot_rigidDataH1Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/bed0ab50-88b6-5e74-a441-3b6771b19e9d
-- title:
--   Artinian W₀-points of R as Igusa root pairs, naturally
-- statement:
--   Fix a prime $q$, natural numbers $\ell_g$ and $M'$ with $\ell_g$ prime, $\ell_g \equiv 11 \pmod{12}$ and $M' \neq 0$, and a commutative ring $A_0$.
--
--   **Transport hypotheses over $A_0$.** Three clauses `hℓ`, `hM`, `hL` require, for every $A_0$-algebra $T$, every Weierstrass curve $W$ over $T$ and every variable change $C$: that `IsGamma1Point W ℓg D` (the affine equation holds at $(x_P,y_P)$, the division polynomial $\mathrm{pre}\Psi_{\ell_g}$ of $W$ vanishes at $x_P$, and $x_Q = x_P$, $y_Q = y_P$) passes to $C \bullet W$ with $D$ replaced by `D.variableChange C`; that `IsGamma0PowAt W p k h` (for $p^k = 2$ the two-torsion-kernel condition, otherwise the cyclic $p^k$-kernel condition: $\deg h \le \varphi(p^k)/2$, the coefficient in that degree is $1$, $h \cdot \mathrm{pre}\Psi_{p^{k-1}} \mid \mathrm{pre}\Psi_{p^{k}}$, and $h$ divides the relevant multiplication numerators) passes to $C \bullet W$ with $h$ replaced by `kernelVariableChangeDeg C (gamma0PowDeg p k) h`; and that a divisibility $h \mid \mathrm{inLineMulPoly}\, W\, \ell_g\, n\, x$ transports to `kernelVariableChangeDeg C d h` dividing $\mathrm{inLineMulPoly}\,(C\bullet W)\,\ell_g\,n\,(u^{-2}(x-r))$.
--
--   **Group-law data.** A family $\mathcal G$ of relative group laws on the projective models of curves with unit discriminant over $A_0$-algebras, assumed chord–tangent (`h𝒢`: a points-evaluation exists in each case) and origin-normalised (`h𝒢O`: the unit section is cut out by an origin-chart ring homomorphism killing $x/y$ and $z/y$); a level transport $\mathcal T$ for $\mathcal G$ at $q$, that is, a functorial action on raw Drinfeld pairs $(W,P,Q)$ compatible with algebra maps and variable changes and preserving the condition that $P,Q$ be a Drinfeld basis of level $q$, together with `h𝒯` asserting that the transported sections are the geometric pullbacks along the corresponding variable-change and coefficient graded homomorphisms.
--
--   **The $H_1$-level moduli package.** $P_0$ is a fine moduli package over $A_0$ for the moduli datum attached to `rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯`: the points over an $A_0$-algebra $T$ are the classes, modulo variable change, of tuples consisting of a Weierstrass curve $W/T$ with unit discriminant, a family of polynomials indexed by the prime factors $p$ of $M'$, a `LevelPData` $D$ and a raw Drinfeld pair, subject to `IsGamma0PowAt` at each $p$ with exponent the $p$-adic valuation of $M'$, `IsGamma1Point W ℓg D`, the Drinfeld level condition, and the link condition `IsGamma1Link` (if $\ell_g$ divides $M'$, the polynomial indexed by $\ell_g$ divides $\mathrm{inLineMulPoly}\,W\,\ell_g\,\ell_g^{v_{\ell_g}(M')-1}\,x_P$); $P_0$ carries a ring $B_0$, a universal point, and the unique-factorisation property through $B_0$.
--
--   **Coefficient rings.** $R$ is a Noetherian local $A_0$-algebra, complete for its maximal ideal, with an $A_0$-algebra map $\iota : B_0 \to R$; $k$ is a field of characteristic $q$ in which $\ell_g$ and $M'$ are invertible; $\mathrm{res}_R : R \to k$ is surjective with kernel the maximal ideal of $R$; $W_0$ is a complete discrete valuation domain with maximal ideal $(q)$, with surjective $\mathrm{res}_0 : W_0 \to k$ of kernel the maximal ideal; $R$ is a $W_0$-algebra, $W_0$ an $A_0$-algebra, the tower $A_0 \to W_0 \to R$ commutes, and $\mathrm{res}_R$ restricts to $\mathrm{res}_0$ on $W_0$ (`hresR₀`). The clause `hfac` states that for every Artinian local $T$ which is a $W_0$- and $A_0$-algebra in the same tower, with residue map $\mathrm{res}_T$ to $k$ surjective of kernel the maximal ideal and restricting to $\mathrm{res}_0$, and every $A_0$-algebra map $\varphi : B_0 \to T$ reducing to $\mathrm{res}_R \circ \iota$, there is a unique $W_0$-algebra map $\Phi : R \to T$ with $\mathrm{res}_T \circ \Phi = \mathrm{res}_R$ and $\Phi \circ \iota = \varphi$.
--
--   **Transport hypotheses over $W_0$.** The clauses `hℓ'`, `hM'`, `hL'` repeat `hℓ`, `hM`, `hL` verbatim with $W_0$ in place of $A_0$; `h𝒢r` and `h𝒢Or` assert that $\mathcal G$ restricted along $A_0 \to W_0$ is chord–tangent and origin-normalised.
--
--   **The étale package and the universal $q$-torsion section.** $P^{\mathrm{et}}$ is a fine moduli package over $W_0$ for the moduli datum of the rigid datum obtained from the product of `gamma0PowComponent W₀ M' hM'`, `gamma1Component W₀ ℓg hℓ'` and the trivial component, restricted by the link condition `IsGamma1Link` on the first two entries; $x^{\mathrm{et}}$ is a raw representative over $P^{\mathrm{et}}.B_0$ whose class is the universal point (`hxet`). $C_Q$ is a commutative ring which is a $P^{\mathrm{et}}.B_0$- and $W_0$-algebra in a tower, $Q_u$ is a section of the projective model of $x^{\mathrm{et}}.\mathrm{curve}$ over $\operatorname{Spec} C_Q$, with $q \cdot Q_u$ the unit section for the restricted group law (`hQu`), and `hrep` asserts that $C_Q$ represents $q$-torsion: for every $P^{\mathrm{et}}.B_0$-algebra $T$ and section $Q$ over $T$, one has $q\cdot Q = O$ exactly when there is a unique $P^{\mathrm{et}}.B_0$-algebra map $\chi : C_Q \to T$ such that $\operatorname{Spec}\chi$ followed by $Q_u$ is $Q$.
--
--   **The torsion-lift ring $S$.** $S$ is a Noetherian local $W_0$-algebra, complete for its maximal ideal, with a $W_0$-algebra map $\iota_S : C_Q \to S$, a surjection $\mathrm{res}_S : S \to k$ with kernel the maximal ideal and restricting to $\mathrm{res}_0$, and a clause `hfacS` of the same shape as `hfac`: Artinian local $W_0$-algebra points of $S$ factor uniquely through $C_Q$ compatibly with residues.
--
--   **Igusa factorisation.** $F_S$ is a formal group over $S$ whose power series is the fixed formal group law of $x^{\mathrm{et}}.\mathrm{curve}$ pushed along $\iota_S \circ (P^{\mathrm{et}}.B_0 \to C_Q)$ (`hFS`); $g \in S[X]$ is monic of degree $q-1$ with all lower coefficients in the maximal ideal and constant coefficient $q$ times a unit; $v$ is a unit power series; and the $q$-th iterate series of $F_S$ factors as $X \cdot g \cdot v$ (`hfacq`). Moreover `AdjoinRoot g` is a domain and $q \neq 0$ in $S$.
--
--   **The residual point.** $k$ is an $A_0$-, $W_0$- and $P^{\mathrm{et}}.B_0$-algebra in a tower, with $W_0 \to k$ equal to $\mathrm{res}_0$; $\rho : B_0 \to k$ equals $\mathrm{res}_R \circ \iota$; $\psi^{\mathrm{et}} : P^{\mathrm{et}}.B_0 \to k$ equals $\mathrm{res}_S \circ \iota_S$ composed with $P^{\mathrm{et}}.B_0 \to C_Q$, and is the structure map to $k$; the reduction of $x^{\mathrm{et}}.\mathrm{curve}$ along $\psi^{\mathrm{et}}$ has unit discriminant $(h\Delta k)$; $Q_k$ is a section of that reduced curve which is pinned to $Q_u$ in the sense of `hQk_pin` (there are a graded homomorphism $\varphi$ between the projective-model gradings and an irrelevant-ideal inclusion such that $\varphi$ is a coefficient homomorphism for $\psi^{\mathrm{et}}$ and $Q_k$ followed by $\mathrm{Proj}.\mathrm{map}\,\varphi$ equals $\operatorname{Spec}(\mathrm{res}_S \circ \iota_S)$ followed by $Q_u$), and $Q_k$ is not the unit section (`hQk`). The reduced level data satisfy the $\Gamma_0(M')$-power conditions at each prime factor of $M'$ (`hhk`), the $\Gamma_1(\ell_g)$-point condition (`hDk`) and the link condition (`hLk`); the raw Drinfeld pair consisting of the reduced curve, the unit section and $Q_k$ is of level $q$ for $\mathcal G$ (`hyk`); and `hρyk` states that pushing the universal point of $P_0$ along $\rho$ gives exactly the class of the raw datum assembled from the reduced curve, $h\Delta k$, the reduced $\Gamma_0(M')$- and $\Gamma_1(\ell_g)$-data and that Drinfeld pair, with level proof $\langle\langle hhk, hDk, hyk\rangle, hLk\rangle$.
--
--   **Conclusion.** There exists a family $\eta$ which assigns to every Artinian local $W_0$-algebra $T$ (with the ring, local-ring, Artinian and algebra structures) and every proof that the composite of the residue map of $T$ with $W_0 \to T$ is surjective, a bijection
--   $$(R \to_{W_0\text{-alg}} T) \;\simeq\; \{\,(p_1,p_2) \in (S \to_{W_0\text{-alg}} T) \times T \;:\; (g \text{ mapped along } p_1)(p_2) = 0\,\},$$
--   and this family is natural in the following sense: for all Artinian local $W_0$-algebras $T$ and $T'$ with surjective residue composites, every $W_0$-algebra map $f : T \to T'$ and every $W_0$-algebra map $\varphi : R \to T$, the pair underlying $\eta_{T'}(f \circ \varphi)$ equals $\bigl(f \circ p_1, f(p_2)\bigr)$, where $(p_1,p_2)$ is the pair underlying $\eta_T(\varphi)$.
--
--   This is the point-counting form of the Igusa description of the completed ordinary stalk at level $\Gamma_0(M') \cap \Gamma_1(\ell_g)$ with Drinfeld $\Gamma(q)$-structure: Artinian local $W_0$-algebra points of $R$ correspond, functorially, to a point of the torsion-lift ring $S$ together with a root of the Igusa polynomial $g$ cutting out the $q$-torsion of the formal group. It is used to produce a $W_0$-algebra isomorphism $R \cong \mathrm{AdjoinRoot}\, g$ in [`ModularCurve.LevelModuliPackageAbs.nonempty_algEquiv_adjoinRoot_of_factorsThrough_of_nthSeries_eq_X_mul_mul_of_isDomain_adjoinRoot_rigidDataH1Pow`](thm.html#ModularCurve.LevelModuliPackageAbs.nonempty_algEquiv_adjoinRoot_of_factorsThrough_of_nthSeries_eq_X_mul_mul_of_isDomain_adjoinRoot_rigidDataH1Pow).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_LevelModuliPackageAbs_exists_algHom_equiv_subtype_eval_map_eq_zero_natural_of_factorsThrough_of_nthSeries_eq_X_mul_mul_of_isDomain_adjoinRoot_rigidDataH1Pow.lean

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
import Definitions.Def_ModularCurve_WeierstrassGamma1Pow
import Definitions.Def_ModularCurve_WeierstrassH1Pow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel IsLocalRing FormalGroup
  AlgebraicGeometry CategoryTheory NeronModelInfra Polynomial

attribute [local instance] MvPolynomial.gradedAlgebra

theorem ModularCurve.LevelModuliPackageAbs.exists_algHom_equiv_subtype_eval_map_eq_zero_natural_of_factorsThrough_of_nthSeries_eq_X_mul_mul_of_isDomain_adjoinRoot_rigidDataH1Pow
    (q : ℕ) [Fact q.Prime] (ℓg M' : ℕ) (hℓg : ℓg.Prime) (hℓg12 : ℓg % 12 = 11) [NeZero M']
    (A₀ : Type) [CommRing A₀]

    (hℓ : ∀ (T : Type) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsGamma1Point W ℓg D →
        ModularCurve.IsGamma1Point (C • W) ℓg (D.variableChange C))
    (hM : ∀ (T : Type) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (hL : ∀ (T : Type) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (d n : ℕ) (h : Polynomial T) (x : T), h ∣ ModularCurve.inLineMulPoly W ℓg n x →
        ModularCurve.kernelVariableChangeDeg C d h ∣
          ModularCurve.inLineMulPoly (C • W) ℓg n (((C.u⁻¹ : Tˣ) : T) ^ 2 * (x - C.r)))
    (𝒢 : GroupLaws A₀) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (𝒯 : LevelTransport A₀ 𝒢 q) (h𝒯 : 𝒯.IsSectionTransport)
    (P₀ : LevelModuliPackageAbs A₀ (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum)
    (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R]
    [Algebra A₀ R] (ι : P₀.B₀ →ₐ[A₀] R)
    (k : Type) [Field k] [CharP k q] (hℓk : ((ℓg : ℕ) : k) ≠ 0) (hM'k : ((M' : ℕ) : k) ≠ 0)
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
      (D : ModularCurve.LevelPData T), ModularCurve.IsGamma1Point W ℓg D →
        ModularCurve.IsGamma1Point (C • W) ℓg (D.variableChange C))
    (hM' : ∀ (T : Type) [CommRing T] [Algebra W₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (hL' : ∀ (T : Type) [CommRing T] [Algebra W₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (d n : ℕ) (h : Polynomial T) (x : T), h ∣ ModularCurve.inLineMulPoly W ℓg n x →
        ModularCurve.kernelVariableChangeDeg C d h ∣
          ModularCurve.inLineMulPoly (C • W) ℓg n (((C.u⁻¹ : Tˣ) : T) ^ 2 * (x - C.r)))

    (h𝒢r : (𝒢.restrictScalars W₀).IsChordTangent) (h𝒢Or : (𝒢.restrictScalars W₀).IsOriginIdentity)
    (Pet : LevelModuliPackageAbs W₀
      ((((ModularCurve.gamma0PowComponent W₀ M' hM').prod
        ((ModularCurve.gamma1Component W₀ ℓg hℓ').prod (ModularCurve.LevelComponent.trivial (A := W₀)))).restrict
        (fun W x => ModularCurve.IsGamma1Link W ℓg M' x.1 x.2.1)
        (fun f _ _ _ hx => ModularCurve.IsGamma1Link.map f.toRingHom hx)
        (fun C W _ _ hx => fun hmem => hL' _ W C _ _ _ _ (hx hmem))).toRigid).toLevelModuliDatum)
    (xet : ((((ModularCurve.gamma0PowComponent W₀ M' hM').prod
        ((ModularCurve.gamma1Component W₀ ℓg hℓ').prod (ModularCurve.LevelComponent.trivial (A := W₀)))).restrict
        (fun W x => ModularCurve.IsGamma1Link W ℓg M' x.1 x.2.1)
        (fun f _ _ _ hx => ModularCurve.IsGamma1Link.map f.toRingHom hx)
        (fun C W _ _ hx => fun hmem => hL' _ W C _ _ _ _ (hx hmem))).toRigid).Raw Pet.B₀)
    (hxet : (Quot.mk _ xet :
      ((((ModularCurve.gamma0PowComponent W₀ M' hM').prod
        ((ModularCurve.gamma1Component W₀ ℓg hℓ').prod (ModularCurve.LevelComponent.trivial (A := W₀)))).restrict
        (fun W x => ModularCurve.IsGamma1Link W ℓg M' x.1 x.2.1)
        (fun f _ _ _ hx => ModularCurve.IsGamma1Link.map f.toRingHom hx)
        (fun C W _ _ hx => fun hmem => hL' _ W C _ _ _ _ (hx hmem))).toRigid).Pt Pet.B₀) =
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
    (hDk : ModularCurve.IsGamma1Point (xet.curve.map ψet.toRingHom) ℓg (xet.level.2.1.map ψet.toRingHom))
    (hLk : ModularCurve.IsGamma1Link (xet.curve.map ψet.toRingHom) ℓg M'
      (fun p => (xet.level.1 p).map ψet.toRingHom) (xet.level.2.1.map ψet.toRingHom))
    (hyk : RawDrinfeldPair.IsLevel 𝒢 q (xet.curve.map ψet.toRingHom)
      ⟨xet.curve.map ψet.toRingHom, (𝒢 k (xet.curve.map ψet.toRingHom) hΔk).one (𝟙 (base (T := k))), Qk⟩)
    (hρyk : (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum.map ρ P₀.univ =
      (Quot.mk _ (⟨xet.curve.map ψet.toRingHom, hΔk,
          ⟨fun p => (xet.level.1 p).map ψet.toRingHom, xet.level.2.1.map ψet.toRingHom,
            ⟨xet.curve.map ψet.toRingHom, (𝒢 k (xet.curve.map ψet.toRingHom) hΔk).one (𝟙 (base (T := k))), Qk⟩⟩,
          ⟨⟨hhk, hDk, hyk⟩, hLk⟩⟩ : (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).Raw k) :
        (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).Pt k)) :
    ∃ η : ∀ (T : Type) [CommRing T] [IsLocalRing T] [IsArtinianRing T] [Algebra W₀ T],
        Function.Surjective (⇑(residue T) ∘ ⇑(algebraMap W₀ T)) →
          ((R →ₐ[W₀] T) ≃ {p : (S →ₐ[W₀] T) × T // (g.map (p.1 : S →+* T)).eval p.2 = 0}),
      ∀ (T : Type) [CommRing T] [IsLocalRing T] [IsArtinianRing T] [Algebra W₀ T]
        (hT : Function.Surjective (⇑(residue T) ∘ ⇑(algebraMap W₀ T)))
        (T' : Type) [CommRing T'] [IsLocalRing T'] [IsArtinianRing T'] [Algebra W₀ T']
        (hT' : Function.Surjective (⇑(residue T') ∘ ⇑(algebraMap W₀ T')))
        (f : T →ₐ[W₀] T') (φ : R →ₐ[W₀] T),
        ((η T' hT' (f.comp φ)).1 : (S →ₐ[W₀] T') × T') = (f.comp (η T hT φ).1.1, f (η T hT φ).1.2) := by sorry
