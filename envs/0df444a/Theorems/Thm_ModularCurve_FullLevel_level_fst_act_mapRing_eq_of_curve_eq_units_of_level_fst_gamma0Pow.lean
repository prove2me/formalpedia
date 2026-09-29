-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_level_fst_act_mapRing_eq_of_curve_eq_units_of_level_fst_gamma0Pow
-- name    : ModularCurve.FullLevel.level_fst_act_mapRing_eq_of_curve_eq_units_of_level_fst_gamma0Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:38.446507+00:00
-- url     : https://prove2.me/theorems/1ac4d870-397d-536f-87ee-bf0292cd2f51
-- title:
--   Level automorphisms fix the Γ₀-slot at the Tate point
-- statement:
--   Numerical and field data. Let $q$ be a prime with $q\ge 5$, let $M'$ be a nonzero natural number with $q\nmid M'$, and let $\ell$ be a prime with $\ell\ge 3$, $\ell\ne q$ and $\ell\nmid M'$. Let $L$ be a field of characteristic zero, let $\xi\in L$ be a primitive $(q\ell)$-th root of unity, and assume (`hιξ`) that there exists a ring homomorphism $\iota\colon L\to\mathbb{C}$ with $\iota\xi=e^{2\pi i/(q\ell)}$. Write $\xi_u$ for $\xi$ regarded as a unit of $L$. Let $K$ be an intermediate field of $L\subseteq \mathrm{LaurentSeries}\,L$ which, by `hK`, is [`ModularCurve.laurentBaseChange L (ModularCurve.xHFunctionField ((q*ℓ)^2*M') (ModularCurve.FullLevel.levelH (q*ℓ) M'))`](def/ModularCurve_LaurentCoeff.html#L103): the field generated over $L$ inside $\mathrm{LaurentSeries}\,L$ by the coefficientwise image of the $q$-expansion function field of level $N_0=(q\ell)^2M'$ attached to the subgroup $H=\ker\bigl((\mathbb{Z}/(q\ell)^2M')^\times\to(\mathbb{Z}/q\ell)^\times\bigr)$, the units congruent to $1$ modulo $q\ell$.
--
--   Base ring. Let $A$ be a discrete valuation domain which is an $L$-algebra with $L$ as its fraction field, with $q$ lying in the maximal ideal of $A$ (`hAq`), equipped with an $A$-algebra structure on $K$ making $A\to L\to K$ a scalar tower. Let $j\in K$ with image [`ModularCurve.coeffEmb L ModularCurve.jq`](def/ModularCurve_LaurentCoeff.html#L81) in $\mathrm{LaurentSeries}\,L$ (the $q$-expansion $q^{-1}+\dots$ of the modular $j$-function transported to $L$), and assume $j\ne 0$. Assume further that $\ell$ and $M'$ are units in $A$ (`hℓA`, `hM'A`).
--
--   Structural hypotheses for the moduli datum. The hypothesis `hℓ` states that for every $A$-algebra $T$, every Weierstrass curve $W$ over $T$, every variable change $C$ and every [`ModularCurve.LevelPData T`](def/ModularCurve_KatzLevelP.html#L43), a level-$\ell$ structure on $W$ transforms into a level-$\ell$ structure on $C\bullet W$ after applying $C$ to the data; `hM` states the analogous compatibility for [`ModularCurve.IsGamma0PowAt`](def/ModularCurve_WeierstrassGamma0Pow.html#L55), namely that if $h\in T[X]$ satisfies `IsGamma0PowAt W p k h` then `kernelVariableChangeDeg C (gamma0PowDeg p k) h` satisfies it for $C\bullet W$. Let $\mathcal{G}$ be a family of relative group laws on the projective models of elliptic curves over $A$-algebras, assumed chord–tangent (`h𝒢`: each group law admits a points evaluation) and origin-normalised (`h𝒢O`: its identity section is given by a ring homomorphism out of the origin chart killing $x/y$ and $z/y$). Let $\mathcal{T}$ be a level-$q$ transport for $\mathcal{G}$ satisfying `IsSectionTransport` (`h𝒯`: the transported Drinfeld sections are compatible with variable changes and with coefficient maps, via the graded homomorphisms of projective model rings). The hypotheses `hVC` and `hCO` provide, for every $A$-algebra $T$ and projective Weierstrass curve over $T$, graded ring homomorphisms of projective model rings realising an arbitrary variable change, resp. an arbitrary $A$-algebra map of coefficients, in the sense of `IsVariableChangeHom` and `IsCoefficientHom`, together with the stated inclusion of irrelevant ideals. These data determine the rigid Weierstrass datum `rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯`, the product of the $\Gamma_0$-power component for $M'$, the level-$\ell$ component and the level-$q$ Drinfeld component; a raw point $x$ over $K$ therefore consists of a Weierstrass curve `x.curve` over $K$ with invertible discriminant together with a triple `x.level` whose first entry `x.level.1` assigns to each prime factor $p$ of $M'$ a polynomial in $K[X]$ satisfying `IsGamma0PowAt x.curve p (M'.factorization p)`, whose second entry `x.level.2.1` is a level-$\ell$ datum and whose third entry `x.level.2.2` is a Drinfeld pair of sections $P,Q$ of level $q$.
--
--   The Tate point. Let $C_0$ be a variable change over $\mathrm{LaurentSeries}\,L$ and let $x$ be a raw point of `rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯` over $K$. Write $(x_v,y_v)=$ [`ModularCurve.cuspPoint L (q*ℓ) ξu v`](def/ModularCurve_KatzLevelPCusps.html#L59) for $v\in(\mathbb{Z}/q\ell)^2$. The hypothesis `hx` consists of five clauses. First, a normalisation of $C_0$: $u\cdot(2x_{(1,0)}+C(6^{-1}))=2y_{(1,0)}+x_{(1,0)}$ for $u=C_0.u$, together with $C_0.r=C(-12^{-1})$, $C_0.s=C(-2^{-1})$, $C_0.t=C(24^{-1})$. Second, the image of `x.curve` in $\mathrm{LaurentSeries}\,L$ equals $C_0\bullet$ [`ModularCurve.tateBase L (q*ℓ)`](def/ModularCurve_TateSlots.html#L46). Third, the image of the level-$\ell$ datum `x.level.2.1` equals `(ModularCurve.cuspData L (q*ℓ) ξu ![q,0] ![0,-q]).variableChange C₀`. Fourth, there exist $P_x,P_y,Q_x,Q_y\in K$ whose images in $\mathrm{LaurentSeries}\,L$ are the four coordinates `xP`, `yP`, `xQ`, `yQ` of `(ModularCurve.cuspData L (q*ℓ) ξu ![ℓ,0] ![0,-ℓ]).variableChange C₀`, and such that `IsSectionThrough x.level.2.2.P Px Py` and `IsSectionThrough x.level.2.2.Q Qx Qy` hold, i.e. the two Drinfeld sections pass through the affine points $(P_x,P_y)$ and $(Q_x,Q_y)$. Fifth, the $j$-invariant of the class of $x$ under `toLevelModuliDatum.jOf` has image [`ModularCurve.jqNModC L (q*ℓ)`](def/ModularCurve_JqCoeff.html#L18) in $\mathrm{LaurentSeries}\,L$, the $j$-series with $q$ replaced by $q^{q\ell}$.
--
--   The hypothesis `hx6` describes the $\Gamma_0$-slot of $x$ at every cusp datum: for each prime factor $p$ of $M'$, each field $F'$, each ring homomorphism $f\colon L\to F'$ and each primitive $p^{k}$-th root of unity $\zeta\in F'$, where $k=$ `M'.factorization p`, the polynomial `x.level.1 p`, pushed into $\mathrm{LaurentSeries}\,L$ and then transported coefficientwise along $f$, equals
--   $$\mathrm{kernelVariableChangeDeg}\;(C_0\text{ transported along }f)\;(\mathrm{gamma0PowDeg}\ p\,k)\ \prod_{\substack{1\le a\le p^{k}/2\\ p\nmid a}}\bigl(X-C\,(\mathrm{toricPoint}\ F'\,(q\ell)\,(\zeta^{a}))_1\bigr).$$
--
--   The automorphism and the scaling unit. Let $\gamma\in\mathrm{SL}_2(\mathbb{Z})$ with $\gamma\in\Gamma_0(M')$, and let $\tau$ be an $L$-algebra automorphism of $K$ satisfying [`ModularCurve.FullLevel.IsLevelAutAt L (q*ℓ) ξ (q*ℓ) ((q*ℓ)^2*M') (levelH (q*ℓ) M') γ⁻¹ K τ`](def/ModularCurve_FullLevelLevelAutAt.html#L29): for every weight $k\in\mathbb{Z}$, every pair of modular forms $f,g$ of weight $k$ for the group attached to $\Gamma_H$ at level $(q\ell)^2M'$, every pair of integral power series $p_f,p_g$ realising their $q$-expansions with $p_g$ nonzero over $\mathbb{Q}$, and every element of $K$ whose image in $\mathrm{LaurentSeries}\,L$ is the transported quotient $p_f/p_g$, and for every ring homomorphism $\iota\colon L\to\mathbb{C}$ sending $\xi$ to $e^{2\pi i/(q\ell)}$, the image under $\iota$ of $\tau$ applied to that element, multiplied by the $q$-expansion of $g\mid_k$ `conjElemN (q*ℓ) γ⁻¹`, equals the $q$-expansion of $f\mid_k$ `conjElemN (q*ℓ) γ⁻¹`, where `conjElemN m δ` is the matrix $\begin{pmatrix}\delta_{00}&\delta_{01}/m\\ m\,\delta_{10}&\delta_{11}\end{pmatrix}$ in $\mathrm{GL}_2(\mathbb{R})$.
--
--   Let $\mu\in K^\times$ and put $v_\gamma=\bigl(\gamma_{00}\bmod q\ell,\,-\gamma_{10}\bmod q\ell\bigr)$. The hypothesis `hμ` is the identity in $\mathrm{LaurentSeries}\,L$
--   $$\mu\cdot\bigl(2y_{v_\gamma}+x_{v_\gamma}\bigr)\cdot 2\bigl(x_{(1,0)}+C(12^{-1})\bigr)=\bigl(2y_{(1,0)}+x_{(1,0)}\bigr)\cdot 2\bigl(x_{v_\gamma}+C(12^{-1})\bigr).$$
--   Finally, the hypothesis `hc` states that the curve of $\bigl\langle\mu,0,0,0\bigr\rangle\bullet\tau_{*}x$ equals `x.curve`, where $\tau_{*}$ denotes `mapRing` applied to $\tau$ viewed as an $A$-algebra endomorphism of $K$, and $\langle\mu,0,0,0\rangle$ is the variable change with $u=\mu$, $r=s=t=0$.
--
--   Conclusion. Under these hypotheses the first component of the level datum is preserved:
--   $$\bigl(\langle\mu,0,0,0\rangle\bullet\tau_{*}x\bigr).\mathrm{level}.1=x.\mathrm{level}.1 .$$
--   Unfolding the component structures, this says that for every prime factor $p$ of $M'$, with $h_p=$ `x.level.1 p`, $k=$ `M'.factorization p` and $d=$ `gamma0PowDeg p k` $=\varphi(p^{k})/2$ (and $d=1$ when $p^{k}=2$),
--   $$\mu^{-2d}\cdot\bigl(\tau(h_p)\bigr)(\mu^{2}X)=h_p\quad\text{in }K[X],$$
--   where $\tau(h_p)$ denotes the coefficientwise image of $h_p$ under $\tau$. Nothing is asserted about the level-$\ell$ datum or the Drinfeld pair of level $q$.
--
--   This is the $\Gamma_0(M')$-slot half of the identification of the action of a level automorphism $\tau$ attached to $\gamma\in\Gamma_0(M')$ on the Tate point of the rigid Weierstrass moduli problem of level $\Gamma(q\ell)\cap\Gamma_0(M')$ type: once the variable change $\langle\mu,0,0,0\rangle$ has been pinned down by the curve equation `hc`, the $\Gamma_0$-tuple of cyclic-kernel polynomials is unchanged. It is used by [`ModularCurve.FullLevel.exists_variableChange_act_mapRing_eq_relabel_of_isLevelAutAt_of_level_fst_gamma0Pow`](thm.html#ModularCurve.FullLevel.exists_variableChange_act_mapRing_eq_relabel_of_isLevelAutAt_of_level_fst_gamma0Pow), where the three level slots are matched simultaneously to produce the relabelling of the Tate point.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_level_fst_act_mapRing_eq_of_curve_eq_units_of_level_fst_gamma0Pow.lean

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
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_LevelRelabelling
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_KatzLevelPCusps
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel
open scoped MatrixGroups

theorem ModularCurve.FullLevel.level_fst_act_mapRing_eq_of_curve_eq_units_of_level_fst_gamma0Pow
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ))
    (hιξ : ∃ ι : L →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ)))
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M')
        (ModularCurve.FullLevel.levelH (q * ℓ) M')))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]

    (hℓA : IsUnit ((ℓ : ℕ) : A)) (hM'A : IsUnit ((M' : ℕ) : A))
    (hℓ : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsLevelPStructure W ℓ D →
        ModularCurve.IsLevelPStructure (C • W) ℓ (D.variableChange C))
    (hM : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
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
    (C₀ : WeierstrassCurve.VariableChange (LaurentSeries L))
    (x : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).Raw ↥K)
    (hx : haveI : NeZero (q * ℓ) := ⟨Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero⟩

      (((C₀.u : (LaurentSeries L)ˣ) : LaurentSeries L) * (2 * (ModularCurve.cuspPoint L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![1, 0]).1 + HahnSeries.C ((6 : L)⁻¹)) =
          2 * (ModularCurve.cuspPoint L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![1, 0]).2 + (ModularCurve.cuspPoint L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![1, 0]).1 ∧
        C₀.r = HahnSeries.C (-(12 : L)⁻¹) ∧ C₀.s = HahnSeries.C (-(2 : L)⁻¹) ∧ C₀.t = HahnSeries.C ((24 : L)⁻¹)) ∧

      x.curve.map (algebraMap ↥K (LaurentSeries L)) = C₀ • ModularCurve.tateBase L (q * ℓ) ∧

      x.level.2.1.map (algebraMap ↥K (LaurentSeries L)) = (ModularCurve.cuspData L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![(q : ZMod (q * ℓ)), 0] ![0, -(q : ZMod (q * ℓ))]).variableChange C₀ ∧

      (∃ Px Py Qx Qy : ↥K,
        (Px : LaurentSeries L) = ((ModularCurve.cuspData L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![(ℓ : ZMod (q * ℓ)), 0] ![0, -(ℓ : ZMod (q * ℓ))]).variableChange C₀).xP ∧
        (Py : LaurentSeries L) = ((ModularCurve.cuspData L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![(ℓ : ZMod (q * ℓ)), 0] ![0, -(ℓ : ZMod (q * ℓ))]).variableChange C₀).yP ∧
        (Qx : LaurentSeries L) = ((ModularCurve.cuspData L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![(ℓ : ZMod (q * ℓ)), 0] ![0, -(ℓ : ZMod (q * ℓ))]).variableChange C₀).xQ ∧
        (Qy : LaurentSeries L) = ((ModularCurve.cuspData L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![(ℓ : ZMod (q * ℓ)), 0] ![0, -(ℓ : ZMod (q * ℓ))]).variableChange C₀).yQ ∧
        IsSectionThrough x.level.2.2.P Px Py ∧ IsSectionThrough x.level.2.2.Q Qx Qy) ∧

      (((rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.jOf (Quot.mk _ x) : ↥K) : LaurentSeries L) =
        ModularCurve.jqNModC L (q * ℓ))

    (hx6 : haveI : NeZero (q * ℓ) := ⟨Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero⟩
      (∀ (p : ↥M'.primeFactors) (F' : Type) [Field F'] (f : L →+* F') (ζ : F'),
        IsPrimitiveRoot ζ ((p : ℕ) ^ M'.factorization (p : ℕ)) →
        ((x.level.1 p).map (algebraMap ↥K (LaurentSeries L))).map (ModularCurve.coeffMap f) =
          ModularCurve.kernelVariableChangeDeg (C₀.map (ModularCurve.coeffMap f))
            (ModularCurve.gamma0PowDeg (p : ℕ) (M'.factorization (p : ℕ)))
            (∏ a ∈ (Finset.Icc 1 ((p : ℕ) ^ M'.factorization (p : ℕ) / 2)).filter (fun a => ¬ (p : ℕ) ∣ a),
              (Polynomial.X - Polynomial.C (ModularCurve.toricPoint F' (q * ℓ) (ζ ^ a)).1))) )
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M') (τ : ↥K ≃ₐ[L] ↥K)
    (hτ : ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
      (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ)

    (μ : (↥K)ˣ)
    (hμ : (((μ : (↥K)ˣ) : ↥K) : LaurentSeries L) * (2 * (ModularCurve.cuspPoint L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![((γ 0 0 : ℤ) : ZMod (q * ℓ)), -((γ 1 0 : ℤ) : ZMod (q * ℓ))]).2 + (ModularCurve.cuspPoint L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![((γ 0 0 : ℤ) : ZMod (q * ℓ)), -((γ 1 0 : ℤ) : ZMod (q * ℓ))]).1) * (2 * ((ModularCurve.cuspPoint L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![1, 0]).1 + HahnSeries.C ((12 : L)⁻¹))) =
      (2 * (ModularCurve.cuspPoint L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![1, 0]).2 + (ModularCurve.cuspPoint L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![1, 0]).1) * (2 * ((ModularCurve.cuspPoint L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![((γ 0 0 : ℤ) : ZMod (q * ℓ)), -((γ 1 0 : ℤ) : ZMod (q * ℓ))]).1 + HahnSeries.C ((12 : L)⁻¹))))
    (hc : ((rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).act (⟨μ, 0, 0, 0⟩ : WeierstrassCurve.VariableChange ↥K)
            ((rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).mapRing ((τ.toAlgHom : ↥K →ₐ[L] ↥K).restrictScalars A) x)).curve = x.curve) :
    ((rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).act (⟨μ, 0, 0, 0⟩ : WeierstrassCurve.VariableChange ↥K)
            ((rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).mapRing ((τ.toAlgHom : ↥K →ₐ[L] ↥K).restrictScalars A) x)).level.1 = x.level.1 := by sorry
