-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_Diamond_exists_pt_forall_isLevelAutAt_map_eq_act_of_exists_ringHom_rigidDataH1Pow_of_tate_pinGamma1_of_isScalarTower
-- name    : ModularCurve.FullLevel.Diamond.exists_pt_forall_isLevelAutAt_map_eq_act_of_exists_ringHom_rigidDataH1Pow_of_tate_pinGamma1_of_isScalarTower
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:30.533368+00:00
-- url     : https://prove2.me/theorems/c580c792-ab74-51c0-ba07-50ca6cafcd44
-- title:
--   Tate Γ₁(ℓ_g) point identifies level automorphisms with relabelling, sub-base edition
-- statement:
--   **Data.** Fix a prime $q$, a non-zero natural number $M'$ with $q \nmid M'$ (`hqM'`), and a prime $\ell_g$ with $\ell_g \equiv 11 \pmod{12}$ and $\ell_g \mid M'$. Let $L$ be a field of characteristic zero and $\xi \in L$ a primitive $(q\ell_g)$-th root of unity, subject to `hιξ`: some ring homomorphism $\iota : L \to \mathbb{C}$ sends $\xi$ to $\exp(2\pi i/(q\ell_g))$. Let $H_1 \le (\mathbb{Z}/q^2M')^\times$ be, by `hH₁`, the intersection of [`ModularCurve.FullLevel.levelH q M'`](def/ModularCurve_FullLevelJacobian.html#L22) — the kernel of the reduction $(\mathbb{Z}/q^2M')^\times \to (\mathbb{Z}/q)^\times$, i.e. the units congruent to $1$ modulo $q$ — with the kernel of the reduction $(\mathbb{Z}/q^2M')^\times \to (\mathbb{Z}/\ell_g)^\times$. Let $K$ be an intermediate field of $L \subseteq \operatorname{LaurentSeries} L$ which, by `hK`, is [`ModularCurve.laurentBaseChange L (ModularCurve.xHFunctionField (q^2*M') H₁)`](def/ModularCurve_LaurentCoeff.html#L103): the subfield generated over $L$ by the coefficientwise image under $\operatorname{LaurentSeries}\mathbb{Q} \to \operatorname{LaurentSeries}L$ of the $q$-expansion function field of $X_{H_1}$ of level $q^2M'$ over $\mathbb{Q}$. Let $A$ be a discrete valuation domain with fraction field $L$, with $q$ in its maximal ideal (`hAq`), and with an $A$-algebra structure on $K$ compatible with $A \to L \to K$. Let $j \in K$ be a non-zero element whose image in $\operatorname{LaurentSeries}L$ is the coefficientwise image of the rational $j$-series [`ModularCurve.jq`](def/ModularCurve_X0.html#L157) $= t^{-1}\cdot(\text{integral } j\text{-numerator})$ (`hj`).
--
--   **The sub-base.** Let $A_0$ be a commutative ring acting compatibly on $L$, on $K$ and on $A$ (scalar towers $A_0 \to L \to K$ and $A_0 \to A \to K$), such that the images of $\ell_g$ and of $M'$ in $A_0$ are units (`hℓA`, `hM'A`).
--
--   **Functoriality of the three level conditions under variable change.** Hypothesis `hℓ`: for every $A_0$-algebra $T$, Weierstrass curve $W/T$, variable change $C$ and [`ModularCurve.LevelPData`](def/ModularCurve_KatzLevelP.html#L43) $D = (x_P,y_P,x_Q,y_Q)$, if $D$ is a $\Gamma_1(\ell_g)$-point of $W$ — the affine Weierstrass equation holds at $(x_P,y_P)$, $(\operatorname{pre\Psi}_{\ell_g} W)(x_P) = 0$, $x_Q = x_P$ and $y_Q = y_P$ — then the transported data $D^C$ (with $x_P^C = u^{-2}(x_P - r)$, $y_P^C = u^{-3}(y_P - s(x_P-r) - t)$, and likewise for $Q$) is a $\Gamma_1(\ell_g)$-point of $C \bullet W$. Hypothesis `hM`: for every such $T, W, C$, all $p,k \in \mathbb{N}$ and $h \in T[X]$, the condition [`ModularCurve.IsGamma0PowAt W p k h`](def/ModularCurve_WeierstrassGamma0Pow.html#L55) is transported to `IsGamma0PowAt (C • W) p k` of $h^{C} := C(u^{-2d})\, h(C(u^{2})X + C(r))$ with $d =$ `gamma0PowDeg p k` $= 1$ if $p^k = 2$ and $\varphi(p^k)/2$ otherwise; here `IsGamma0PowAt` is the two-torsion kernel condition ($\deg h \le 1$, $h$ has coefficient $1$ in degree $1$, $h \mid \Psi_2^2$) when $p^k = 2$, and otherwise the cyclic-kernel condition `IsCyclicGenKernel` (four clauses, summarised here: $\deg h \le \varphi(p^k)/2$, coefficient $1$ in degree $\varphi(p^k)/2$, $h\cdot\operatorname{pre\Psi}_{p^{k-1}} \mid \operatorname{pre\Psi}_{p^{k}}$, and $h$ divides the multiplication-by-$a$ numerators for $2 \le a \le (p^k-1)/2$ with $p \nmid a$). Hypothesis `hL`: for every such $T, W, C$, all $d,n \in \mathbb{N}$, $h \in T[X]$ and $x \in T$, if $h$ divides [`ModularCurve.inLineMulPoly W ℓg n x`](def/ModularCurve_WeierstrassH1Pow.html#L18) $= \prod_{a=1}^{(\ell_g-1)/2}\bigl(\Phi_n\,C(\Psi_a^2(x)) - C(\Phi_a(x))\,\Psi_n^2\bigr)$, then $h^C$ (as above, with degree parameter $d$) divides `inLineMulPoly (C • W) ℓg n (u^{-2}(x - r))`.
--
--   **Group law and transport package over $A_0$.** Let $\mathcal{G}$ be a family `GroupLaws A₀` assigning to each $A_0$-algebra $T$, projective Weierstrass curve $W/T$ and proof that $\Delta_W$ is a unit a relative group law on the Proj model of $W$; `h𝒢` requires each such group law to admit an identification of its sections over fields with the affine point group that is additive and Galois-equivariant (`IsChordTangent`), and `h𝒢O` requires its identity section to be the origin-chart section at which the coordinates $x/y$ and $z/y$ both vanish (`IsOriginIdentity`). Let $\mathcal{T}$ be a `LevelTransport A₀ 𝒢 q`: a functorial transport of raw Drinfeld pairs (a projective curve together with two sections) along $A_0$-algebra maps and along variable changes, preserving the condition that the two sections form a Drinfeld $q$-basis for $\mathcal{G}$; `h𝒯` (`IsSectionTransport`, two clauses) requires the transported sections to be the pullbacks of the original ones along the graded maps of Proj models induced by variable-change homomorphisms, respectively by coefficient homomorphisms. Hypotheses `hVC` and `hCO` assert the existence of such graded ring homomorphisms: for every $A_0$-algebra $T$, projective curve $W$ and variable change $C$ (respectively every $A_0$-algebra map $f : T \to T'$) a graded homomorphism from the graded quotient ring of $W$ to that of $C \bullet W$ (respectively of $W$ mapped along $f$) satisfying the irrelevant-ideal inclusion and `IsVariableChangeHom` (respectively `IsCoefficientHom`).
--
--   Write $\mathcal{R} =$ `rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯` for the resulting rigid Weierstrass data over $A_0$: its raw objects over an $A_0$-algebra $T$ consist of a Weierstrass curve with unit discriminant together with a triple — a family of polynomials $h_p \in T[X]$ indexed by the prime factors $p$ of $M'$ satisfying `IsGamma0PowAt` at $p^{v_p(M')}$, a `LevelPData` which is a $\Gamma_1(\ell_g)$-point, and a raw Drinfeld pair which is a Drinfeld $q$-basis for $\mathcal{G}$ on that curve — subject to the link condition that $h_{\ell_g}$ divides `inLineMulPoly W ℓg (ℓg ^ (M'.factorization ℓg - 1)) x_P`; its points over $T$ are the classes of raw objects modulo the variable-change action, and `jOf` is the $j$-invariant of the underlying curve.
--
--   **The relabelling action.** Let $\rho$ assign to each $\gamma \in \Gamma_0(M')$ an automorphism of the moduli problem $\mathcal{R}$ (a natural self-map of the point functor preserving $j$). Hypothesis `hρ` prescribes $\rho$ on points over fields: for every $\gamma \in \Gamma_0(M')$, every field $T$ which is an $A_0$-algebra, raw objects $x, x'$ over $T$ and a proof $h_\Delta$ that the discriminant of the curve of the Drinfeld-pair component of $x$ is a unit, if $x'$ and $x$ have the same curve, the same $\Gamma_0$-component $h_\bullet$, the affine point of $x'$ attached to $(x'_P)$ equals $\gamma_{00}$ times the affine point attached to $(x_P)$ on the base change of $x$'s curve to $T$, $x'$ satisfies $x_Q' = x_P'$ and $y_Q' = y_P'$, and the Drinfeld-pair component of $x'$ is the $\mathcal{G}$-relabelling of that of $x$ by $\gamma$ (i.e. $P \mapsto \gamma_{00}P + \gamma_{10}Q$, $Q \mapsto \gamma_{01}P + \gamma_{11}Q$), then $\rho(\gamma)$ sends the class of $x$ to the class of $x'$.
--
--   **Conclusion.** There exists a point $x_0$ of $\mathcal{R}$ over $K$ with the following properties.
--
--   (1) The image of $j(x_0) \in K$ in $\operatorname{LaurentSeries}L$ is [`ModularCurve.jqNModC L q`](def/ModularCurve_JqCoeff.html#L18), the $j$-series over $L$ with the exponents multiplied by $q$.
--
--   (2) There are a variable change $C$ over $\operatorname{LaurentSeries}L$ and a raw object $r$ over $K$ such that the class of $r$ is $x_0$ and the following hold. Write $(x_\ell, y_\ell) =$ [`ModularCurve.tateToricPoint L q`](def/ModularCurve_KatzLevelPCusps.html#L20) evaluated at the unit $\xi^{q}$ (of multiplicative order $\ell_g$), and $\zeta_q = \xi^{\ell_g}$ (of order $q$).
--
--   (2a) $C$ is normalised by: $u\,(2x_\ell + 1/6) = 2y_\ell + x_\ell$ for $u = C.u$, together with $C.r = -1/12$, $C.s = -1/2$, $C.t = 1/24$, the constants being constant Laurent series.
--
--   (2b) The curve of $r$, pushed to $\operatorname{LaurentSeries}L$, equals $C \bullet$ [`ModularCurve.tateBase L q`](def/ModularCurve_TateSlots.html#L46), the Tate curve with exponents scaled by $q$.
--
--   (2c) For every prime factor $p$ of $M'$, every field $F'$, every ring homomorphism $f : L \to F'$ and every primitive $p^{v_p(M')}$-th root of unity $\zeta \in F'$: the $p$-component polynomial of $r$, pushed to $\operatorname{LaurentSeries}L$ and then mapped coefficientwise along $f$, equals the transport by $C$ mapped along $f$, with degree parameter `gamma0PowDeg p (M'.factorization p)`, of the monic polynomial $\prod_a (X - x_a)$, where $a$ runs over the integers in $[1, p^{v_p(M')}/2]$ not divisible by $p$ and $x_a$ is the first coordinate of [`ModularCurve.toricPoint F' q (ζ ^ a)`](def/ModularCurve_TateSlots.html#L125).
--
--   (2d) The $\Gamma_1(\ell_g)$-component of $r$, pushed to $\operatorname{LaurentSeries}L$, equals the transport by $C$ of the level data $(x_\ell, y_\ell, x_\ell, y_\ell)$.
--
--   (2e) There are $P_x, P_y, Q_x, Q_y \in K$ whose images in $\operatorname{LaurentSeries}L$ are the four coordinates $x_P, y_P, x_Q, y_Q$ of the transport by $C$ of [`ModularCurve.cuspData L q (ξ^ℓg) ![1,0] ![0,-1]`](def/ModularCurve_KatzLevelPCusps.html#L71) — the level data whose $P$ is the toric point at $\zeta_q$ and whose $Q$ is the non-toric point attached to $\zeta_q^{0}$ and the second coordinate $-1$ — and such that the two sections of the Drinfeld-pair component of $r$ pass through $(P_x,P_y)$ and $(Q_x,Q_y)$ in the sense of `IsSectionThrough` (each section factors through the $z$-chart via a ring homomorphism whose affine coordinates are the given values).
--
--   (3) For every $\gamma \in \mathrm{SL}_2(\mathbb{Z})$ lying in $\Gamma_0(M')$ and every $L$-algebra automorphism $\tau$ of $K$ satisfying [`ModularCurve.FullLevel.IsLevelAutAt L q (ξ ^ ℓg) q (q ^ 2 * M') H₁ γ⁻¹ K τ`](def/ModularCurve_FullLevelLevelAutAt.html#L29) — that is, for every weight $k$, all modular forms $f,g$ of weight $k$ for the group $\Gamma_{H_1}(q^2M')$ viewed in $\mathrm{GL}_2(\mathbb{R})$, all integral power series $p_f, p_g$ that are the $q$-expansions of $f$ and $g$ with the Laurent series of $p_g$ non-zero, every $x \in K$ whose Laurent series is the coefficientwise image of $p_f/p_g$, and every ring homomorphism $\iota : L \to \mathbb{C}$ with $\iota(\xi^{\ell_g}) = \exp(2\pi i/q)$, the coefficientwise $\iota$-image of $\tau(x)$ times the $q$-expansion of $g\mid_k \begin{pmatrix} a & b/q \\ qc & d\end{pmatrix}$ equals the $q$-expansion of $f\mid_k \begin{pmatrix} a & b/q \\ qc & d\end{pmatrix}$, where $\begin{pmatrix} a& b\\ c& d\end{pmatrix} = \gamma^{-1}$ — one has
--   $$\mathcal{R}\text{-functoriality along } \tau \ (\text{as an } A_0\text{-algebra map}) \ \text{applied to } x_0 \; = \; \rho(\gamma).\mathrm{act}\,(x_0).$$
--
--   This is the automorphism-identification step for the $\Gamma_1(\ell_g)$-guarded moduli problem: over the cuspidal Laurent-series chart it produces the Tate-curve point with prescribed $\Gamma_0(M')$, $\Gamma_1(\ell_g)$ and Drinfeld $q$-basis structures at the cusp, and identifies every level automorphism of $K$ attached to $\gamma \in \Gamma_0(M')$ with the diamond-type relabelling action $\rho(\gamma)$ on that moduli problem. It is the edition in which the moduli data, group laws and transports are based on an arbitrary sub-base $A_0$ mapping to $L$, $K$ and $A$, and it feeds the classification of level automorphisms on the stalk of the moduli package at the cusp.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_Diamond_exists_pt_forall_isLevelAutAt_map_eq_act_of_exists_ringHom_rigidDataH1Pow_of_tate_pinGamma1_of_isScalarTower.lean

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
attribute [local instance 10000] SubalgebraClass.toAlgebra Algebra.toSMul Algebra.toModule

theorem ModularCurve.FullLevel.Diamond.exists_pt_forall_isLevelAutAt_map_eq_act_of_exists_ringHom_rigidDataH1Pow_of_tate_pinGamma1_of_isScalarTower
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

    (A₀ : Type) [CommRing A₀] [Algebra A₀ L] [Algebra A₀ ↥K] [IsScalarTower A₀ L ↥K]
    [Algebra A₀ A] [IsScalarTower A₀ A ↥K]

    (hℓA : IsUnit ((ℓg : ℕ) : A₀)) (hM'A : IsUnit ((M' : ℕ) : A₀))
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

    (hVC : ∀ (T : Type) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve.Projective T) (C : WeierstrassCurve.VariableChange T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (C • W))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • W)) ≤ (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsVariableChangeHom W C φ)
    (hCO : ∀ (T T' : Type) [CommRing T] [Algebra A₀ T] [CommRing T'] [Algebra A₀ T'] (f : T →ₐ[A₀] T')
      (W : WeierstrassCurve.Projective T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f.toRingHom))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f.toRingHom)) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsCoefficientHom W f.toRingHom φ)
    (ρ : ↥(CongruenceSubgroup.Gamma0 M') → (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum.ProblemAut)

    (hρ : ∀ (γ : ↥(CongruenceSubgroup.Gamma0 M')) (T : Type) [Field T] [DecidableEq T] [Algebra A₀ T]
      (x x' : (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).Raw T) (hΔ : IsUnit x.level.2.2.curve.Δ),
      x'.curve = x.curve →
      x'.level.1 = x.level.1 →
      ModularCurve.LevelRelabelling.toPoint ((x.curve).baseChange T) x'.level.2.1.xP x'.level.2.1.yP =
        (((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) 0 0) •
          ModularCurve.LevelRelabelling.toPoint ((x.curve).baseChange T) x.level.2.1.xP x.level.2.1.yP →
      x'.level.2.1.xQ = x'.level.2.1.xP → x'.level.2.1.yQ = x'.level.2.1.yP →
      x'.level.2.2 = ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel 𝒢
        ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) x.level.2.2 hΔ →
      (ρ γ).act (Quot.mk _ x) = Quot.mk _ x') :
    ∃ x₀ : (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum.Pt ↥K,
      (((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum.jOf x₀ : ↥K) : LaurentSeries L) = ModularCurve.jqNModC L q ∧

      (haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
      ∃ (C : WeierstrassCurve.VariableChange (LaurentSeries L)) (r : (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).Raw ↥K),
      (Quot.mk _ r : (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum.Pt ↥K) = x₀ ∧

      (((C.u : (LaurentSeries L)ˣ) : LaurentSeries L) * (2 * (ModularCurve.tateToricPoint L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ q)).1 + HahnSeries.C ((6 : L)⁻¹)) =
          2 * (ModularCurve.tateToricPoint L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ q)).2 + (ModularCurve.tateToricPoint L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ q)).1 ∧
        C.r = HahnSeries.C (-(12 : L)⁻¹) ∧ C.s = HahnSeries.C (-(2 : L)⁻¹) ∧ C.t = HahnSeries.C ((24 : L)⁻¹)) ∧

      r.curve.map (algebraMap ↥K (LaurentSeries L)) = C • ModularCurve.tateBase L q ∧

      (∀ (p : ↥M'.primeFactors) (F' : Type) [Field F'] (f : L →+* F') (ζ : F'),
        IsPrimitiveRoot ζ ((p : ℕ) ^ M'.factorization (p : ℕ)) →
        ((r.level.1 p).map (algebraMap ↥K (LaurentSeries L))).map (ModularCurve.coeffMap f) =
          ModularCurve.kernelVariableChangeDeg (C.map (ModularCurve.coeffMap f))
            (ModularCurve.gamma0PowDeg (p : ℕ) (M'.factorization (p : ℕ)))
            (∏ a ∈ (Finset.Icc 1 ((p : ℕ) ^ M'.factorization (p : ℕ) / 2)).filter (fun a => ¬ (p : ℕ) ∣ a),
              (Polynomial.X - Polynomial.C (ModularCurve.toricPoint F' q (ζ ^ a)).1))) ∧

      r.level.2.1.map (algebraMap ↥K (LaurentSeries L)) =
        (⟨(ModularCurve.tateToricPoint L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ q)).1,
          (ModularCurve.tateToricPoint L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ q)).2,
          (ModularCurve.tateToricPoint L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ q)).1,
          (ModularCurve.tateToricPoint L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ q)).2⟩ :
            ModularCurve.LevelPData (LaurentSeries L)).variableChange C ∧

      (∃ Px Py Qx Qy : ↥K,
        (Px : LaurentSeries L) = ((ModularCurve.cuspData L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ ℓg) ![(1 : ZMod q), 0] ![0, -(1 : ZMod q)]).variableChange C).xP ∧
        (Py : LaurentSeries L) = ((ModularCurve.cuspData L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ ℓg) ![(1 : ZMod q), 0] ![0, -(1 : ZMod q)]).variableChange C).yP ∧
        (Qx : LaurentSeries L) = ((ModularCurve.cuspData L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ ℓg) ![(1 : ZMod q), 0] ![0, -(1 : ZMod q)]).variableChange C).xQ ∧
        (Qy : LaurentSeries L) = ((ModularCurve.cuspData L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ ℓg) ![(1 : ZMod q), 0] ![0, -(1 : ZMod q)]).variableChange C).yQ ∧
        IsSectionThrough r.level.2.2.P Px Py ∧ IsSectionThrough r.level.2.2.Q Qx Qy)) ∧
      ∀ (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M') (τ : ↥K ≃ₐ[L] ↥K),
        ModularCurve.FullLevel.IsLevelAutAt L q (ξ ^ ℓg) q (q ^ 2 * M') H₁ γ⁻¹ K τ →
          (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum.map ((τ.toAlgHom : ↥K →ₐ[L] ↥K).restrictScalars A₀) x₀ = (ρ ⟨γ, hγ⟩).act x₀ := by sorry
