-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_Diamond_exists_variableChange_act_mapRing_eq_relabel_of_isLevelAutAt_of_level_fst_rigidDataH1Pow
-- name    : ModularCurve.FullLevel.Diamond.exists_variableChange_act_mapRing_eq_relabel_of_isLevelAutAt_of_level_fst_rigidDataH1Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:30.533368+00:00
-- url     : https://prove2.me/theorems/83055662-bbd3-5c24-9268-86a14a07a9e6
-- title:
--   Level automorphism at γ⁻¹ realises the diamond relabelling
-- statement:
--   **Arithmetic setting.** Let $q$ be a prime, $M'\ge 1$ with $q\nmid M'$, and let $\ell_g$ be a prime with $\ell_g\equiv 11\pmod{12}$ and $\ell_g\mid M'$. Let $L$ be a field of characteristic zero and $\xi\in L$ a primitive $(q\ell_g)$-th root of unity, and assume (hypothesis `hιξ`) that some ring homomorphism $\iota:L\to\mathbb C$ sends $\xi$ to $e^{2\pi i/(q\ell_g)}$. Let $H_1\le(\mathbb Z/q^2M')^\times$ be the subgroup $H_1=\mathrm{levelH}\,q\,M'\cap\ker\big((\mathbb Z/q^2M')^\times\to(\mathbb Z/\ell_g)^\times\big)$, i.e. (unfolding [`ModularCurve.FullLevel.levelH`](def/ModularCurve_FullLevelJacobian.html#L22)) the group of units of $\mathbb Z/q^2M'$ that are congruent to $1$ modulo $q$ and congruent to $1$ modulo $\ell_g$. Let $K$ be the intermediate field of $L\subseteq L((\mathsf q))$ generated over $L$ by the image, under coefficientwise extension of scalars $\mathbb Q\to L$, of the $q$-expansion function field over $\mathbb Q$ of the modular curve $X_{H_1}$ of level $q^2M'$ (hypothesis `hK`). Let $A$ be a discrete valuation domain with an $A$-algebra structure on $L$ making $L$ its fraction field, with $q$ in the maximal ideal of $A$, together with an $A$-algebra structure on $K$ compatible with that on $L$. Let $j\in K$ be the element whose image in $L((\mathsf q))$ is the coefficientwise image of the $q$-expansion [`ModularCurve.jq`](def/ModularCurve_X0.html#L157) of the $j$-function, assumed nonzero. Finally, $\ell_g$ and $M'$ are assumed to be units in $A$ (`hℓA`, `hM'A`).
--
--   **Moduli data and their pins.** The hypotheses `hℓ`, `hM`, `hL` are the three variable-change compatibilities used to assemble the level structure over $A$: stability of the predicate [`ModularCurve.IsGamma1Point`](def/ModularCurve_WeierstrassGamma1Pow.html#L10) for $\ell_g$ under $D\mapsto D.\mathrm{variableChange}\,C$, stability of [`ModularCurve.IsGamma0PowAt`](def/ModularCurve_WeierstrassGamma0Pow.html#L55) at every $(p,k)$ under $h\mapsto \mathrm{kernelVariableChangeDeg}\,C\,(\mathrm{gamma0PowDeg}\,p\,k)\,h$, and the statement that if $h\mid \mathrm{inLineMulPoly}\,W\,\ell_g\,n\,x$ then $\mathrm{kernelVariableChangeDeg}\,C\,d\,h$ divides $\mathrm{inLineMulPoly}\,(C\bullet W)\,\ell_g\,n\,(u^{-2}(x-r))$. Let $\mathcal G$ be a family of relative group laws on the projective Weierstrass models over $A$-algebras with unit discriminant, assumed chord–tangent (`h𝒢`: on each base the law is computed by a points-evaluation) and origin-normalised (`h𝒢O`: its unit section is the section of the $Y$-chart at which $X/Y$ and $Z/Y$ vanish); let $\mathcal T$ be a transport of raw Drinfeld pairs for $\mathcal G$ at $q$, assumed to be a section transport (`h𝒯`: the transported $P$ and $Q$ pull back to the original ones along any graded homomorphism realising the variable change, resp. the coefficient change). The hypotheses `hVC` and `hCO` assert that such realising graded homomorphisms exist in all cases, with the irrelevant ideal of the target contained in the image of that of the source. Write $\mathcal R:=\mathrm{rigidDataH1Pow}\,A\,\ell_g\,M'\,q\,h\ell\,hM\,hL\,\mathcal G\,\mathcal T$ for the resulting rigid Weierstrass datum; a raw point $x\in\mathcal R.\mathrm{Raw}\,K$ consists of a Weierstrass curve $x.\mathrm{curve}$ over $K$ with unit discriminant, a family $x.\mathrm{level}.1$ of polynomials indexed by the prime factors $p$ of $M'$ which are $\Gamma_0(p^{v_p(M')})$-kernel polynomials, a `LevelPData` $x.\mathrm{level}.2.1$ which is a $\Gamma_1(\ell_g)$-point, a raw Drinfeld pair $x.\mathrm{level}.2.2$ which is a Drinfeld basis of level $q$ for $\mathcal G$, and the link condition that $x.\mathrm{level}.1$ at $\ell_g$ divides $\mathrm{inLineMulPoly}\,(x.\mathrm{curve})\,\ell_g\,\ell_g^{v_{\ell_g}(M')-1}\,(x.\mathrm{level}.2.1).xP$.
--
--   **The Tate pin.** Let $C_0$ be a variable change over $L((\mathsf q))$ and $x\in\mathcal R.\mathrm{Raw}\,K$. Write $\zeta_{\ell_g}$ for the unit $\xi^{q}$ and $\zeta_q$ for the unit $\xi^{\ell_g}$, and $P=(P_x,P_y):=\mathrm{tateToricPoint}\,L\,q\,\zeta_{\ell_g}$, the explicitly defined pair of Laurent series. The hypothesis `hx` is the conjunction of five clauses: (i) $u_{C_0}\,(2P_x+\tfrac16)=2P_y+P_x$ together with $r_{C_0}=-\tfrac1{12}$, $s_{C_0}=-\tfrac12$, $t_{C_0}=\tfrac1{24}$ (constants in $L((\mathsf q))$); (ii) the image of $x.\mathrm{curve}$ in $L((\mathsf q))$ equals $C_0\bullet\mathrm{tateBase}\,L\,q$, the Tate curve with parameter $\mathsf q^{\,q}$; (iii) the image of $x.\mathrm{level}.2.1$ equals the $C_0$-variable change of the `LevelPData` $\langle P_x,P_y,P_x,P_y\rangle$; (iv) there exist $P'_x,P'_y,Q'_x,Q'_y\in K$ whose images in $L((\mathsf q))$ are, respectively, the four entries $xP,yP,xQ,yQ$ of the $C_0$-variable change of $\mathrm{cuspData}\,L\,q\,\zeta_q\,(1,0)\,(0,-1)$ — so the $P$-entries are the toric point at $\zeta_q$ and the $Q$-entries the point [`ModularCurve.nonToricPoint`](def/ModularCurve_TateSlots.html#L35) at $\zeta_q^0$ with exponent $(-1:\mathbb Z/q)$ — and the sections $x.\mathrm{level}.2.2.P$ and $x.\mathrm{level}.2.2.Q$ pass through $(P'_x,P'_y)$, resp. $(Q'_x,Q'_y)$, in the sense of `IsSectionThrough` (there is a homomorphism from the $Z$-chart ring to $K$ cutting out the section and taking $X/Z$, $Y/Z$ to the prescribed values); (v) the image in $L((\mathsf q))$ of $\mathcal R.\mathrm{toLevelModuliDatum}.\mathrm{jOf}$ of the class of $x$ — that is, of the $j$-invariant of $x.\mathrm{curve}$ — is $\mathrm{jqNModC}\,L\,q$, the $j$-expansion in $\mathsf q^{\,q}$.
--
--   **The $\Gamma_0(M')$-component pin.** The hypothesis `hx6` states: for every prime factor $p$ of $M'$, every field $F'$, every ring homomorphism $f:L\to F'$ and every primitive $p^{v_p(M')}$-th root of unity $\zeta\in F'$, the image of $x.\mathrm{level}.1\,p$ in $L((\mathsf q))$, pushed forward coefficientwise along $f$, equals $\mathrm{kernelVariableChangeDeg}$ of $C_0$ pushed along $f$, at degree $\mathrm{gamma0PowDeg}\,p\,v_p(M')$, applied to $\prod_{a}\big(X-(\mathrm{toricPoint}\,F'\,q\,(\zeta^a))_1\big)$, the product being over $1\le a\le p^{v_p(M')}/2$ with $p\nmid a$.
--
--   **The level automorphism.** Let $\gamma\in SL_2(\mathbb Z)$ lie in $\Gamma_0(M')$ and let $\tau$ be an $L$-algebra automorphism of $K$ satisfying $\mathrm{IsLevelAutAt}\,L\,q\,(\xi^{\ell_g})\,q\,(q^2M')\,H_1\,\gamma^{-1}\,K\,\tau$: for every weight $k\in\mathbb Z$, all modular forms $f,g$ of weight $k$ for $\Gamma_{H_1}(q^2M')$ with integral $q$-expansion power series $p_f,p_g$, with the Laurent series attached to $p_g$ nonzero, every $y\in K$ whose image in $L((\mathsf q))$ is the coefficientwise image of $p_f/p_g$, and every $\iota:L\to\mathbb C$ with $\iota(\xi^{\ell_g})=e^{2\pi i/q}$, one has $\iota$ applied coefficientwise to $\tau(y)$, times the $q$-expansion of $g\mid_k\mathrm{conjElemN}\,q\,\gamma^{-1}$, equal to the $q$-expansion of $f\mid_k\mathrm{conjElemN}\,q\,\gamma^{-1}$, where $\mathrm{conjElemN}\,q\,\delta$ is the matrix $\begin{pmatrix}\delta_{00}&\delta_{01}/q\\ q\,\delta_{10}&\delta_{11}\end{pmatrix}$.
--
--   **Conclusion.** There exist a variable change $C_\tau$ over $K$ and a proof $h_\Delta$ that the discriminant of $x.\mathrm{level}.2.2.\mathrm{curve}$ is a unit such that, writing $y:=\mathcal R.\mathrm{act}\,C_\tau\big(\mathcal R.\mathrm{mapRing}\,(\tau\text{ viewed as an }A\text{-algebra map }K\to K)\,x\big)$, the following six statements hold:
--
--   1. $y.\mathrm{curve}=x.\mathrm{curve}$;
--
--   2. $y.\mathrm{level}.1=x.\mathrm{level}.1$, i.e. the family of $\Gamma_0(p^{v_p(M')})$-kernel polynomials is unchanged;
--
--   3. $\mathrm{toPoint}$ of $(y.\mathrm{level}.2.1.xP,\;y.\mathrm{level}.2.1.yP)$ on the base change of $x.\mathrm{curve}$ to $K$ equals $\gamma_{00}$ times $\mathrm{toPoint}$ of $(x.\mathrm{level}.2.1.xP,\;x.\mathrm{level}.2.1.yP)$ on the same curve, where $\gamma_{00}$ is the $(0,0)$-entry of $\gamma$ acting by the integer scalar action on the group of affine points, and $\mathrm{toPoint}$ sends a pair of coordinates to the corresponding affine point when it is nonsingular and to $0$ otherwise;
--
--   4. $y.\mathrm{level}.2.1.xQ=y.\mathrm{level}.2.1.xP$;
--
--   5. $y.\mathrm{level}.2.1.yQ=y.\mathrm{level}.2.1.yP$;
--
--   6. $y.\mathrm{level}.2.2=\mathrm{RawDrinfeldPair.relabel}\,\mathcal G\,\gamma\,(x.\mathrm{level}.2.2)\,h_\Delta$, that is, the Drinfeld pair of $y$ has the same curve as that of $x$ and its two sections are the $\mathbb Z$-linear combinations $\gamma_{00}P+\gamma_{10}Q$ and $\gamma_{01}P+\gamma_{11}Q$ formed with the group law $\mathcal G$ on that curve.
--
--   This is the $H_1$-level step identifying the effect on a raw $H_1$-moduli datum, pinned at the Tate curve with parameter $\mathsf q^{\,q}$, of the automorphism $\tau$ of the function field $K$ that implements $\gamma^{-1}\in\Gamma_0(M')$ on $q$-expansions: up to a change of variables over $K$ it fixes the curve and the $\Gamma_0(M')$-kernel polynomials, multiplies the $\Gamma_1(\ell_g)$-point by $\gamma_{00}$, and relabels the Drinfeld $\Gamma(q)$-basis by the matrix $\gamma$. It feeds the constructions of a problem automorphism attached to such a $\tau$ and of the associated place-and-residue data, and the auxiliary level-one comparison at the Tate point.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_Diamond_exists_variableChange_act_mapRing_eq_relabel_of_isLevelAutAt_of_level_fst_rigidDataH1Pow.lean

import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_LevelRelabelling
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_KatzLevelPCusps
import Definitions.Def_ModularCurve_WeierstrassGamma1Pow
import Definitions.Def_ModularCurve_WeierstrassH1Pow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel
open scoped MatrixGroups

theorem ModularCurve.FullLevel.Diamond.exists_variableChange_act_mapRing_eq_relabel_of_isLevelAutAt_of_level_fst_rigidDataH1Pow
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓg : ℕ) (hℓg : ℓg.Prime) (hℓg12 : ℓg % 12 = 11) (hℓgM' : ℓg ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓg))
    (hιξ : ∃ ι : L →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓg)))
    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓgM' (q ^ 2))).ker)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField (q ^ 2 * M') H₁))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]

    (hℓA : IsUnit ((ℓg : ℕ) : A)) (hM'A : IsUnit ((M' : ℕ) : A))
    (hℓ : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsGamma1Point W ℓg D →
        ModularCurve.IsGamma1Point (C • W) ℓg (D.variableChange C))
    (hM : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (hL : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (d n : ℕ) (h : Polynomial T) (x : T), h ∣ ModularCurve.inLineMulPoly W ℓg n x →
        ModularCurve.kernelVariableChangeDeg C d h ∣
          ModularCurve.inLineMulPoly (C • W) ℓg n (((C.u⁻¹ : Tˣ) : T) ^ 2 * (x - C.r)))
    (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (𝒯 : LevelTransport A 𝒢 q) (h𝒯 : 𝒯.IsSectionTransport)

    (hVC : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve.Projective T) (C : WeierstrassCurve.VariableChange T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (C • W))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • W)) ≤ (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsVariableChangeHom W C φ)
    (hCO : ∀ (T T' : Type) [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T')
      (W : WeierstrassCurve.Projective T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f.toRingHom))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f.toRingHom)) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsCoefficientHom W f.toRingHom φ)
    [DecidableEq ↥K]
    (C₀ : WeierstrassCurve.VariableChange (LaurentSeries L))
    (x : (rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).Raw ↥K)
    (hx : haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩

      (((C₀.u : (LaurentSeries L)ˣ) : LaurentSeries L) * (2 * (ModularCurve.tateToricPoint L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ q)).1 + HahnSeries.C ((6 : L)⁻¹)) =
          2 * (ModularCurve.tateToricPoint L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ q)).2 + (ModularCurve.tateToricPoint L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ q)).1 ∧
        C₀.r = HahnSeries.C (-(12 : L)⁻¹) ∧ C₀.s = HahnSeries.C (-(2 : L)⁻¹) ∧ C₀.t = HahnSeries.C ((24 : L)⁻¹)) ∧

      x.curve.map (algebraMap ↥K (LaurentSeries L)) = C₀ • ModularCurve.tateBase L q ∧

      x.level.2.1.map (algebraMap ↥K (LaurentSeries L)) =
        (⟨(ModularCurve.tateToricPoint L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ q)).1,
          (ModularCurve.tateToricPoint L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ q)).2,
          (ModularCurve.tateToricPoint L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ q)).1,
          (ModularCurve.tateToricPoint L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ q)).2⟩ :
            ModularCurve.LevelPData (LaurentSeries L)).variableChange C₀ ∧

      (∃ Px Py Qx Qy : ↥K,
        (Px : LaurentSeries L) = ((ModularCurve.cuspData L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ ℓg) ![(1 : ZMod q), 0] ![0, -(1 : ZMod q)]).variableChange C₀).xP ∧
        (Py : LaurentSeries L) = ((ModularCurve.cuspData L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ ℓg) ![(1 : ZMod q), 0] ![0, -(1 : ZMod q)]).variableChange C₀).yP ∧
        (Qx : LaurentSeries L) = ((ModularCurve.cuspData L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ ℓg) ![(1 : ZMod q), 0] ![0, -(1 : ZMod q)]).variableChange C₀).xQ ∧
        (Qy : LaurentSeries L) = ((ModularCurve.cuspData L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ ℓg) ![(1 : ZMod q), 0] ![0, -(1 : ZMod q)]).variableChange C₀).yQ ∧
        IsSectionThrough x.level.2.2.P Px Py ∧ IsSectionThrough x.level.2.2.Q Qx Qy) ∧

      (((rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum.jOf (Quot.mk _ x) : ↥K) : LaurentSeries L) =
        ModularCurve.jqNModC L q)

    (hx6 : haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
      (∀ (p : ↥M'.primeFactors) (F' : Type) [Field F'] (f : L →+* F') (ζ : F'),
        IsPrimitiveRoot ζ ((p : ℕ) ^ M'.factorization (p : ℕ)) →
        ((x.level.1 p).map (algebraMap ↥K (LaurentSeries L))).map (ModularCurve.coeffMap f) =
          ModularCurve.kernelVariableChangeDeg (C₀.map (ModularCurve.coeffMap f))
            (ModularCurve.gamma0PowDeg (p : ℕ) (M'.factorization (p : ℕ)))
            (∏ a ∈ (Finset.Icc 1 ((p : ℕ) ^ M'.factorization (p : ℕ) / 2)).filter (fun a => ¬ (p : ℕ) ∣ a),
              (Polynomial.X - Polynomial.C (ModularCurve.toricPoint F' q (ζ ^ a)).1))) )
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M') (τ : ↥K ≃ₐ[L] ↥K)
    (hτ : ModularCurve.FullLevel.IsLevelAutAt L q (ξ ^ ℓg) q (q ^ 2 * M') H₁ γ⁻¹ K τ) :
    ∃ Cτ : WeierstrassCurve.VariableChange ↥K,
      ∃ hΔ : IsUnit x.level.2.2.curve.Δ,
        ((rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).act Cτ
            ((rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ((τ.toAlgHom : ↥K →ₐ[L] ↥K).restrictScalars A) x)).curve = x.curve ∧
        ((rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).act Cτ
            ((rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ((τ.toAlgHom : ↥K →ₐ[L] ↥K).restrictScalars A) x)).level.1 = x.level.1 ∧
        ModularCurve.LevelRelabelling.toPoint ((x.curve).baseChange ↥K)
            ((rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).act Cτ
            ((rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ((τ.toAlgHom : ↥K →ₐ[L] ↥K).restrictScalars A) x)).level.2.1.xP
            ((rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).act Cτ
            ((rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ((τ.toAlgHom : ↥K →ₐ[L] ↥K).restrictScalars A) x)).level.2.1.yP =
          (((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0) •
            ModularCurve.LevelRelabelling.toPoint ((x.curve).baseChange ↥K) x.level.2.1.xP x.level.2.1.yP ∧
        ((rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).act Cτ
            ((rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ((τ.toAlgHom : ↥K →ₐ[L] ↥K).restrictScalars A) x)).level.2.1.xQ =
          ((rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).act Cτ
            ((rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ((τ.toAlgHom : ↥K →ₐ[L] ↥K).restrictScalars A) x)).level.2.1.xP ∧
        ((rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).act Cτ
            ((rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ((τ.toAlgHom : ↥K →ₐ[L] ↥K).restrictScalars A) x)).level.2.1.yQ =
          ((rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).act Cτ
            ((rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ((τ.toAlgHom : ↥K →ₐ[L] ↥K).restrictScalars A) x)).level.2.1.yP ∧
        ((rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).act Cτ
            ((rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ((τ.toAlgHom : ↥K →ₐ[L] ↥K).restrictScalars A) x)).level.2.2 =
          ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel 𝒢 ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) x.level.2.2 hΔ := by sorry
