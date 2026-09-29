-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_residue_mem_riemannRochSpace_sub_and_hasValue_of_mem_riemannRochSpace_sub_of_annulus_offDiag_of_wgen
-- name    : ModularCurve.XHDRModelAtP.residue_mem_riemannRochSpace_sub_and_hasValue_of_mem_riemannRochSpace_sub_of_annulus_offDiag_of_wgen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/3f0e08e8-704b-5778-a750-1bc8456f3b9d
-- title:
--   Residues at a node of bi-integral sections of L(D₀-E)
-- statement:
--   Throughout, $\bar{\mathbb Q}$ denotes `AlgebraicClosure ℚ`, $F_M$ the field $\mathrm{xHFunctionFieldBar}\,M\,H$ (the base change to $\bar{\mathbb Q}$ of the $q$-expansion function field of level $\Gamma_H(M)$), $F_{M/p}$ the corresponding field for level $M/p$ and the image subgroup `infSubgroup p M H hpM`, $\kappa$ the residue field of the valuation subring $A$, and $\bar F$ the field `JHNeronObjectAtP.Fbar p M H hpM κ` $=\;\mathrm{qExpFunctionFieldC}\,\kappa\,(\Gamma_N)$. A `Place` of a field extension is a valuation subring containing the image of the base field, distinct from the whole field and with principal ideals; $v.\mathrm{ord}$ is the associated normalised integer valuation, and $\mathrm{riemannRochSpace}\,D$ is the space of $f$ with $v(f)\le\exp(D v)$ for all places $v$, i.e. $\mathrm{ord}_v f\ge -D(v)$.
--
--   **Level data.** A prime $p$ and $M\neq 0$ with $p\mid M$ (`hpM`) and $p^2\nmid M$ (`hpM2`); a subgroup $H\le(\mathbb Z/M)^\times$ such that every unit of $\mathbb Z/M$ mapping to $1$ in $(\mathbb Z/(M/p))^\times$ lies in $H$ (`hHp`); $M/p\neq0$; and `hj`, the assertion that the $q$-expansion `jqModC ℚ` lies in the level-$\mathrm{SL}(2,\mathbb Z)$ function field $\mathrm{qExpFunctionFieldC}\,\mathbb Q\,\top$.
--
--   **The integral model.** A term $\mathfrak X$ of `XHDRModelAtP p M H hpM hj`. This structure packages: properness, flatness, local finite presentation of the structure map of the two-chart integral model at level $\Gamma_M(H)$ and integrality of its total space, integral closedness of the sections over every affine open, properness and smoothness of relative dimension $1$ at level $\Gamma_N$; a curve model $\mathfrak X.\mathrm{Meta}$ over $\bar{\mathbb Q}$ whose function field is identified with $F_M$ (a `CurveModel` carries, besides the proper smooth integral scheme, the identification of its function field, a bijection `placeOfPoint` from closed points to places, and the compatibility of stalks with valuation subrings), an isomorphism $\mathfrak X.\mathrm{eeta}$ of $\mathfrak X.\mathrm{Meta}.C$ with the base change of the integral model to $\bar{\mathbb Q}$ compatible with the structure maps, Galois equivariance of the induced point–place bijection `pointEquivPlace`, the pinning of the chart algebra against Laurent-series coefficients, smoothness and geometric integrality of the generic fibre, and further fields used below: an automorphism $\mathfrak X.w$ of the generic fibre, and for $A,\rho$ as below the special-fibre curve model $\mathfrak X.\mathrm{Mfib}\,A\,hA\,\rho\,h\rho$ together with the morphisms $\mathfrak X.\mathrm{efib}$ and the two component maps $\mathfrak X.\mathrm{comp}\,A\,hA\,\rho\,h\rho\,i$, $i\in\mathrm{Fin}\,2$.
--
--   **The place at $p$.** A valuation subring $A$ of $\bar{\mathbb Q}$ with `hA : A.LiesOverPrime p`, i.e. $p$ is a non-unit of $A$; the residue field $\kappa$ is of characteristic $p$ and algebraically closed; and a ring homomorphism $\rho: R_p\to A$ with $A.\mathrm{subtype}\circ\rho$ equal to the structure map $R_p\to\bar{\mathbb Q}$ (`hρ`).
--
--   **The diamond.** A unit $pb$ of $\mathbb Z/(M/p)$ representing the class of $p$ (`hpb`), and a self-map $\delta$ of the places of $\bar F$ over $\kappa$ which, by `hδ`, is the action of the semilinear automorphism attached to the diamond automorphism $\mathrm{diamondActionModL}\,\kappa\,(M/p)\,(\mathrm{infSubgroup}\,p\,M\,H\,hpM)$ evaluated at the lift $\mathrm{gammaLift}\,(M/p)\,pb$.
--
--   **The node pairs.** A finite set $SS$ of pairs of places of $\bar F$ over $\kappa$ which, by `hSS`, consists exactly of the members of $\mathrm{ssNodePairsQExp}\,\kappa\,\Gamma_N\,p$, that is of the pairs $(s_1,s_2)$ with $s_2\in\mathrm{ssPlacesQExp}\,\kappa\,\Gamma_N\,p$ and $s_1=\mathrm{qExpFrobeniusPlaceModL}\,\kappa\,\Gamma_N\,p\,(s_2)$.
--
--   **Degeneracy maps and specialisation.** A $\bar{\mathbb Q}$-algebra automorphism $\theta$ of $F_M$; a $\bar{\mathbb Q}$-algebra map $\alpha: F_{M/p}\to F_M$ with `hα : α.IsIntegral`, and $\beta:=\theta\circ\alpha$ with `hβ : β.IsIntegral`; a place-specialisation datum $P_{sp}$ of type `JHPlaceSpecialization p M H hpM A`, consisting of a map $\mathrm{sp}$ from places of $F_{M/p}$ over $\bar{\mathbb Q}$ to places of $\bar F$ over $\kappa$ together with a homomorphism on degree-zero divisor classes, subject to the compatibility of $\mathrm{sp}$ with orders of $q$-expansions reduced modulo the maximal ideal, surjectivity of $\mathrm{sp}$, realisability of push-forward divisors as divisors of functions, invariance under the inertia subgroup of $A$ over $\mathbb Q$, transformation into the $q$-expansion Frobenius place under a Frobenius element at $p$, and compatibility of the two maps on degree-zero classes; and a prolongation datum $R_{pd}$ of type `JHPlaceSpecialization.ProlongationDatum Psp θ`, consisting of two regular prolongations $R_1,R_2$ of $A$ in $F_M$ with residue field $\bar F$, such that Laurent series integral over $A$ have $R_1$-residue the coefficientwise reduction, that $f\in R_2$-integers iff $\theta f\in R_1$-integers, and that the $R_2$-residue of $f$ equals the $R_1$-residue of $\theta f$. The two readings of a place $W$ of $F_M$ are $P_{sp}.\mathrm{reduceFst}\,\alpha\,h\alpha\,W=\mathrm{sp}(W|_\alpha)$ and $P_{sp}.\mathrm{reduceSnd}\,\beta\,h\beta\,\delta\,W=\delta(\mathrm{sp}(W|_\beta))$, where $W|_\varphi$ denotes restriction along $\varphi$; $W$ is *strict of the first kind* when $\delta(\mathrm{Frob}(\mathrm{reduceFst}\,W))=\mathrm{reduceSnd}\,W$ and $\mathrm{reduceFst}\,W$ is not $\delta$-fixed, *strict of the second kind* when $\mathrm{reduceFst}\,W=\mathrm{Frob}(\mathrm{reduceSnd}\,W)$ and $\mathrm{reduceSnd}\,W$ is not $\delta$-fixed; $\mathrm{fstDiv}\,D$ and $\mathrm{sndDiv}\,D$ are the restrictions of a divisor $D$ to the places strict of the first, respectively second, kind.
--
--   **Structural hypotheses.** `hwgen`: for any two sections $y,y'$ of $\mathfrak X.\mathrm{Meta}.\mathrm{toBase}$, if the generic-fibre point attached to $y'$ followed by $\mathfrak X.w$ agrees with that attached to $y$, then $\mathrm{pointEquivPlace}\,y'$ is the image of $\mathrm{pointEquivPlace}\,y$ under the semilinear automorphism of $\theta$. `hα_coe`: $\alpha$ is the identity on Laurent series, $(\alpha u)=u$ as elements of $\mathrm{LaurentSeries}\,\bar{\mathbb Q}$. `hβ_coe`: $\beta u$ has Laurent series $\mathrm{qExpand}\,\bar{\mathbb Q}\,p$ applied to that of $u$, i.e. $\beta$ is the $q\mapsto q^p$ degeneracy. `hθgal`: $\theta$ commutes with the arithmetic Galois action of every $\sigma\in\mathrm{Gal}(\bar{\mathbb Q}/\mathbb Q)$ on $F_M$. `hTD`: the type dichotomy, i.e. for every place $W$ of $F_M$ either $\mathrm{reduceFst}\,W=\mathrm{Frob}(\mathrm{reduceSnd}\,W)$ or $\delta(\mathrm{Frob}(\mathrm{reduceFst}\,W))=\mathrm{reduceSnd}\,W$. `hmodel`: $R_{pd}$ is a model for $(\alpha,\beta,\delta)$, the conjunction of the two divisor laws and the two cusp laws at $\infty$ and at $0$. `hO`: the order law at $\delta$-fixed affine places — for $f$ integral for both prolongations with both residues non-zero and $D$ the divisor of $f$, the push-forward $\mathrm{mapDomain}(\mathrm{reduceFst})D$ at such a place $v$ equals $\mathrm{ord}_v$ of the $R_1$-residue plus $\mathrm{ord}_{\delta(\mathrm{Frob}\,v)}$ of the $R_2$-residue. `hRL`: the regularity law for $SS$ — non-negativity of the orders of the two residues at $\delta$-fixed affine places where all preimages under $\mathrm{reduceFst}$ have non-negative order, and, for each $s\in SS$, existence of a common value $c$ of the two residues at $s_1$ and $s_2$ under the same non-negativity assumption. `hNV`: the node-value law for $SS$ — the same common value, with $c\neq 0$, whenever no place in the divisor of $f$ reduces to $(s_1,s_2)$ under $(\mathrm{reduceFst},\mathrm{reduceSnd})$.
--
--   **Fibre compatibility.** Two hypotheses with the same binders: $i\in\mathrm{Fin}\,2$, a section $y$ of $\mathfrak X.\mathrm{Meta}.\mathrm{toBase}$, an $A$-point $u$ of the integral model over $\mathrm{Spec}\,\rho$ whose induced $\bar{\mathbb Q}$-point is the generic-fibre point of $y$, a $\kappa$-point $u_\kappa$ of the fibre over $(\mathrm{residue}\circ\rho)$ which is a section and whose first projection is the reduction of $u$, and a closed point $P_0$ of $(\mathfrak X.\mathrm{Mfib}\,A\,hA\,\rho\,h\rho).C$ whose image under $\mathfrak X.\mathrm{efib}$ followed by the $i$-th component map is the closed point underlying $u_\kappa$. Under these, `hcompat` states that the place of $P_0$ in the fibre curve model is $\mathrm{reduceFst}(\mathrm{pointEquivPlace}\,y)$ if $i=0$ and $\mathrm{reduceSnd}(\mathrm{pointEquivPlace}\,y)$ otherwise, and `hcompat'` states that for $i=0$ one has $\mathrm{reduceSnd}(\mathrm{pointEquivPlace}\,y)=\delta(\mathrm{Frob}(\text{place of }P_0))$ while for $i\neq0$ one has $\mathrm{reduceFst}(\mathrm{pointEquivPlace}\,y)=\mathrm{Frob}(\text{place of }P_0)$, with $\mathrm{Frob}=\mathrm{qExpFrobeniusPlaceModL}\,\kappa\,\Gamma_N\,p$.
--
--   **The node and its annulus.** A pair $s\in SS$ (`hs`); an integer $e_s>0$; an annulus $\mathrm{An}$ of type [`AlgebraicCurve.Annulus A F_M`](def/AlgebraicCurve_SemistableCharts.html#L86), consisting of a set $\mathrm{An}.\mathrm{dom}$ of places of $F_M$, a parameter $\mathrm{An}.\mathrm{param}\in F_M$ and a modulus $\mathrm{An}.\mathrm{modulus}$ in the maximal ideal of $A$, subject to the annulus axioms: every place of the domain is rational, the parameter is integral there with value in the maximal ideal of $A$, non-zero, and dividing the modulus; every admissible value is attained by a unique place of the domain; the parameter minus its value has order $1$; and the unit principle for functions with vanishing order along the domain. The annulus data are constrained by: `hdom`, which says that $W\in\mathrm{An}.\mathrm{dom}$ if and only if $\mathrm{reduceFst}\,W=s_1$ and $W$ is strict of neither kind; `hmodulus`, that the modulus is $p^{e_s}$ times a unit of $A$; `hinert`, that the parameter is fixed by the arithmetic Galois action of every element of the inertia subgroup of $A$ over $\mathbb Q$; `hz₁`, that $\mathrm{modulus}^{-1}\cdot\mathrm{param}$ lies in the $R_1$-integers; `hz₂`, that $\mathrm{param}$ lies in the $R_2$-integers with non-zero residue; `hatt₂`, the second attachment law, that $\mathrm{ord}_{s_2}$ of the $R_2$-residue of $\mathrm{param}$ is $1$ and that for every $f$ in the $R_2$-integers with non-zero residue and with $\mathrm{ord}_P f=0$ for all $P\in\mathrm{An}.\mathrm{dom}$, the element $P.\mathrm{evalAt}\,f\cdot(P.\mathrm{evalAt}\,\mathrm{param})^{-\mathrm{ord}_{s_2}(\text{residue of }f)}$ lies in $A$ and is a unit there, for every $P\in\mathrm{An}.\mathrm{dom}$; and `hatt₁`, the same statement with $R_1$, $s_1$ and the function $\mathrm{modulus}\cdot\mathrm{param}^{-1}$ in place of $R_2$, $s_2$ and $\mathrm{param}$.
--
--   **The divisor and the leading datum.** A finitely supported function $E$ on the places of $F_M$ with $E(V)\neq0$ only for $V\in\mathrm{An}.\mathrm{dom}$ (`hE`) and $E\ge0$ pointwise (`hE0`); an integer $m$ and a unit $u$ of $A$ with the leading-coefficient identity `hlead`: $u\cdot\mathrm{modulus}^{m}=\prod_V\bigl(-V.\mathrm{evalAt}\,\mathrm{An}.\mathrm{param}\bigr)^{E(V)}$ in $\bar{\mathbb Q}$.
--
--   **Conclusion.** For every divisor $D_0$ on $F_M$ over $\bar{\mathbb Q}$ with $0\le D_0$ and $P_{sp}.\mathrm{IsGoodDiv}$, that is every place in the support of $D_0$ is strict of the first or of the second kind, and for every $G\in F_M$ lying in the $R_1$-integers (witness $h_1$) and in the $R_2$-integers (witness $h_2$) and belonging to $\mathrm{riemannRochSpace}(D_0-E)$, the following four assertions hold.
--
--   First, the $R_1$-residue of $G$ lies in $\mathrm{riemannRochSpace}\bigl(\mathrm{mapDomain}(\mathrm{reduceFst})(\mathrm{fstDiv}\,D_0)-\mathrm{single}\,s_1\,m\bigr)$.
--
--   Second, the $R_2$-residue of $G$ lies in $\mathrm{riemannRochSpace}\bigl(\mathrm{mapDomain}(\mathrm{reduceSnd})(\mathrm{sndDiv}\,D_0)-\mathrm{single}\,s_2\,(\deg E-m)\bigr)$, where $\deg E=\sum_V E(V)$.
--
--   Third, for every $t\in SS$ with $t\neq s$ there is $c\in\kappa$ such that the $R_1$-residue of $G$ has value $c$ at $t_1$ and the $R_2$-residue of $G$ has value $c$ at $t_2$ (here $v.\mathrm{HasValue}\,g\,c$ means $g$ is in the valuation subring of $v$ and its residue is the image of $c$).
--
--   Fourth, there exists $\lambda\in\kappa$ such that the product of the $R_2$-residue of $G$ with the $(-(\deg E-m))$-th power of the $R_2$-residue of $\mathrm{An}.\mathrm{param}$ has value $\lambda$ at $s_2$, and the product of the $R_1$-residue of $G$ with the $(-m)$-th power of the $R_1$-residue of $\mathrm{modulus}\cdot\mathrm{An}.\mathrm{param}^{-1}$ has value $\mathrm{residue}(u)\cdot\lambda$ at $s_1$.
--
--   This is the restriction half of the analysis of the Deligne–Rapoport model of $X_H(M)$ at a prime $p$ exactly dividing $M$, where the special fibre consists of two copies of the level-$M/p$ curve crossing at the supersingular points: a function integral for both Gauss prolongations $R_1,R_2$ and lying in $L(D_0-E)$ restricts to sections of the correspondingly twisted line bundles on the two components, with matching values at all nodes other than the chosen one and with the leading values at that node related by the unit $u$ of the leading-coefficient identity. It is used by [`ModularCurve.XHDRModelAtP.exists_forall_exists_mem_riemannRochSpace_sub_and_residue_eq_of_hasValue_leading_of_nonneg_of_annulus_offDiag_of_wgen`](thm.html#ModularCurve.XHDRModelAtP.exists_forall_exists_mem_riemannRochSpace_sub_and_residue_eq_of_hasValue_leading_of_nonneg_of_annulus_offDiag_of_wgen), the converse lifting statement, which adds a dimension count on the special fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_residue_mem_riemannRochSpace_sub_and_hasValue_of_mem_riemannRochSpace_sub_of_annulus_offDiag_of_wgen.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_ComponentGroup
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve
  IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP
open scoped MatrixGroups

theorem ModularCurve.XHDRModelAtP.residue_mem_riemannRochSpace_sub_and_hasValue_of_mem_riemannRochSpace_sub_of_annulus_offDiag_of_wgen
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)

    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v)

    (SS : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) ×
      Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (hSS : ∀ s, s ∈ SS ↔ s ∈ ssNodePairsQExp (ResidueField ↥A) (ΓN p M H hpM) p)

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : (θ.toAlgHom.comp α).IsIntegral)
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)

    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
          y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
          𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hTD : Psp.TypeDichotomy α (θ.toAlgHom.comp α) hα hβ δ) (hmodel : Rpd.IsModel α (θ.toAlgHom.comp α) hα hβ δ)

    (hcompat : ∀ (i : Fin 2)
        (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
        (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
        (_ : barPt A ≫ u.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
        (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
        (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
        (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
        (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C)
        (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A))),
        (𝔛.Mfib A hA ρ hρ).placeOfPoint P0 =
          if i = 0 then Psp.reduceFst α hα (𝔛.Meta.pointEquivPlace y)
          else Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ (𝔛.Meta.pointEquivPlace y))
    (hcompat' : ∀ (i : Fin 2)
        (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
        (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
        (_ : barPt A ≫ u.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
        (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
        (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
        (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
        (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C)
        (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A))),
        if i = 0 then
          Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ (𝔛.Meta.pointEquivPlace y) =
            δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint P0))
        else
          Psp.reduceFst α hα (𝔛.Meta.pointEquivPlace y) =
            qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint P0))

    (hO : Rpd.OrderLawFixed α (θ.toAlgHom.comp α) hα hβ δ)
    (hRL : Rpd.RegularityLaw α (θ.toAlgHom.comp α) hα hβ δ SS) (hNV : Rpd.NodeValueLaw α (θ.toAlgHom.comp α) hα hβ δ SS)

    (hθgal : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (f : ↥(xHFunctionFieldBar M H)),
      θ (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • f) =
        arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • θ f)

    (hβ_coe : ∀ u, (((θ.toAlgHom.comp α) u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))

    (s : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) ×
      Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) (hs : s ∈ SS)
    (es : ℕ) (hes : 0 < es) (An : AlgebraicCurve.Annulus A ↥(xHFunctionFieldBar M H))
    (hdom : ∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
      W ∈ An.dom ↔ (Psp.reduceFst α hα W = s.1 ∧ ¬ Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W ∧ ¬ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ W))
    (hmodulus : ∃ u : ↥A, IsUnit u ∧ An.modulus = ((p : ℕ) : ↥A) ^ es * u)
    (hinert : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.inertiaSubgroupIn ℚ →
      (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • An.param = An.param)
    (hz₁ : algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((An.modulus : AlgebraicClosure ℚ))⁻¹ * An.param ∈ Rpd.R₁.integers)
    (hz₂ : ∃ h₂ : An.param ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨An.param, h₂⟩ ≠ 0)
    (hatt₂ : ∃ h₂ : An.param ∈ Rpd.R₂.integers, s.2.ord (Rpd.R₂.residue ⟨An.param, h₂⟩) = 1 ∧
      ∀ (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨f, hf⟩ ≠ 0 →
        (∀ P ∈ An.dom, P.ord f = 0) → ∀ P ∈ An.dom,
          ∃ h : P.evalAt f * (P.evalAt An.param) ^ (-(s.2.ord (Rpd.R₂.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A))
    (hatt₁ : ∃ h₁ : algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((An.modulus : ↥A) : AlgebraicClosure ℚ) * An.param⁻¹ ∈ Rpd.R₁.integers,
      s.1.ord (Rpd.R₁.residue ⟨_, h₁⟩) = 1 ∧
      ∀ (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨f, hf⟩ ≠ 0 →
        (∀ P ∈ An.dom, P.ord f = 0) → ∀ P ∈ An.dom,
          ∃ h : P.evalAt f * (P.evalAt (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((An.modulus : ↥A) : AlgebraicClosure ℚ) * An.param⁻¹)) ^
            (-(s.1.ord (Rpd.R₁.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A))

    (E : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) →₀ ℤ) (hE : ∀ V, E V ≠ 0 → V ∈ An.dom)
    (hE0 : ∀ V, 0 ≤ E V)
    (m : ℤ) (u : ↥A) (hu : IsUnit u)
    (hlead : ((u : ↥A) : AlgebraicClosure ℚ) * ((An.modulus : ↥A) : AlgebraicClosure ℚ) ^ m
      = E.prod (fun V n => (-(V.evalAt An.param)) ^ n))
    :
    ∀ (D₀ : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), 0 ≤ D₀ →
      Psp.IsGoodDiv α (θ.toAlgHom.comp α) hα hβ δ D₀ →
      ∀ (G : ↥(xHFunctionFieldBar M H)) (h₁ : G ∈ Rpd.R₁.integers) (h₂ : G ∈ Rpd.R₂.integers),
        G ∈ riemannRochSpace (D₀ - E) →
        Rpd.R₁.residue ⟨G, h₁⟩ ∈ riemannRochSpace (Finsupp.mapDomain (Psp.reduceFst α hα) (Psp.fstDiv α (θ.toAlgHom.comp α) hα hβ δ D₀) - Finsupp.single s.1 m) ∧
        Rpd.R₂.residue ⟨G, h₂⟩ ∈ riemannRochSpace (Finsupp.mapDomain (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ) (Psp.sndDiv α (θ.toAlgHom.comp α) hα hβ δ D₀) - Finsupp.single s.2 ((E.sum fun _ n => n) - m)) ∧

        (∀ t ∈ SS, t ≠ s → ∃ c : ResidueField ↥A, t.1.HasValue (Rpd.R₁.residue ⟨G, h₁⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) c ∧
          t.2.HasValue (Rpd.R₂.residue ⟨G, h₂⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) c) ∧

        (∃ lam : ResidueField ↥A,
          s.2.HasValue ((Rpd.R₂.residue ⟨G, h₂⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) *
            (Rpd.R₂.residue ⟨An.param, hz₂.fst⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) ^ (-((E.sum fun _ n => n) - m))) lam ∧
          s.1.HasValue ((Rpd.R₁.residue ⟨G, h₁⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) *
            (Rpd.R₁.residue ⟨_, hatt₁.fst⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) ^ (-m)) (IsLocalRing.residue ↥A u * lam)) := by sorry
