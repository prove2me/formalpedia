-- Prove2me | Theorems.Thm_ModularCurve_LevelModuliPackageAbs_exists_algEquiv_comp_eq_classify_act_of_problemAut_relabel_of_factorsThrough_rigidDataH1Pow
-- name    : ModularCurve.LevelModuliPackageAbs.exists_algEquiv_comp_eq_classify_act_of_problemAut_relabel_of_factorsThrough_rigidDataH1Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/1c07d182-3a31-57d2-83cc-1c2085ff4242
-- title:
--   Relabelling automorphism of the rigidified ring R
-- statement:
--   Fix a prime $q$, a nonzero $M'$, and a prime $\ell_g$ with $\ell_g\equiv 11\pmod{12}$ and $\ell_g\mid M'$, and a base ring $A_0$ in which $\ell_g$ is invertible. Let $h\ell$, $hM$, $hL$ be the transport hypotheses asserting that, over any $A_0$-algebra $T$, a variable change $C$ carries a $\Gamma_1$-point datum $D$ (a quadruple $(x_P,y_P,x_Q,y_Q)$ with $(x_P,y_P)$ on $W$, $\operatorname{pre}\Psi_{\ell_g}(x_P)=0$, $x_Q=x_P$, $y_Q=y_P$) to one for $C\bullet W$, a cyclic or two-torsion kernel polynomial for $(p,k)$ to `kernelVariableChangeDeg C (gamma0PowDeg p k)` of it, and a divisor of `inLineMulPoly W ℓg n x` to a divisor of the corresponding polynomial for $C\bullet W$. Let $\mathcal G$ be a family of relative group laws on the projective models, chord–tangent and with the origin as identity, and $\mathcal T$ a level transport of Drinfeld pairs at $q$ with the section-transport property; assume further that variable changes and coefficient maps are realised by graded ring homomorphisms of the projective-model graded rings surjective onto the irrelevant ideal in the stated sense ($hVC$, $hCO$). Let $P_0=(B_0,\mathrm{univ})$ be a fine moduli package for the moduli datum attached to `rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯`, whose $T$-points are Weierstrass curves with invertible discriminant equipped with a $\Gamma_0$-kernel polynomial for each prime factor of $M'$, a $\Gamma_1$-point datum at $\ell_g$, and a Drinfeld basis of level $q$, linked by the divisibility of the $\ell_g$-polynomial into `inLineMulPoly`, taken up to variable change; let $x$ be a raw point over $B_0$ whose class is $\mathrm{univ}$. Let $R$ be a noetherian local domain, complete for its maximal ideal, an $A_0$-algebra with an $A_0$-algebra map $\iota:B_0\to R$, let $k$ be a field of characteristic $q$ in which $\ell_g$ and $M'$ are nonzero, $\mathrm{res}_R:R\to k$ surjective with kernel $\mathfrak m_R$, and let $W_0$ be a complete discrete valuation ring with maximal ideal $(q)$ and surjection $\mathrm{res}_0:W_0\to k$ with kernel $\mathfrak m_{W_0}$, with $R$ a $W_0$-algebra compatibly over $A_0$ and $\mathrm{res}_R\circ\mathrm{alg}_{W_0\to R}=\mathrm{res}_0$; assume $\iota$ has the factorisation property $hfac$: for every artinian local $W_0$- and $A_0$-algebra $T$ with a residue map to $k$ compatible with $\mathrm{res}_0$ and every $A_0$-algebra map $\varphi:B_0\to T$ whose residue agrees with that of $\iota$, there is a unique $W_0$-algebra map $\Phi:R\to T$ with residue $\mathrm{res}_R$ and $\Phi\circ\iota=\varphi$. Finally let $\gamma\in\Gamma_0(M')\subseteq \mathrm{SL}_2(\mathbb Z)$ and let $\rho_\gamma$ be an automorphism of the moduli problem pinned by $hpin$: over any field $T$ that is an $A_0$-algebra, for raw points $y,y'$ with the discriminant of the curve of the Drinfeld component of $y$ invertible, agreeing curves and $\Gamma_0$-components, with the $\Gamma_1$-point of $y'$ equal to $\gamma_{00}$ times that of $y$ on the base change of the curve, with $x_Q=x_P$, $y_Q=y_P$ for $y'$, and with the Drinfeld pair of $y'$ the $\gamma$-relabelling of that of $y$, one has $\rho_\gamma\cdot[y]=[y']$; and assume $\iota(\mathrm{classify}(\rho_\gamma\cdot\mathrm{univ})\,b)\equiv\iota(b)\pmod{\mathfrak m_R}$ for all $b\in B_0$. Then there exists a $W_0$-algebra automorphism $\theta_0$ of $R$ with $\theta_0(\iota(b))=\iota(\mathrm{classify}(\rho_\gamma\cdot\mathrm{univ})\,b)$ for all $b\in B_0$ and $\theta_0(r)\equiv r\pmod{\mathfrak m_R}$ for all $r\in R$.
--
--   This is the descent of a diamond-type relabelling by $\gamma\in\Gamma_0(M')$ from the level structures to the rigidified ring $R$: the induced map on the coordinate ring of the moduli package extends, uniquely by the factorisation property, to an automorphism of $R$ over the coefficient ring $W_0$ which is the identity modulo the maximal ideal. It feeds the analysis of the action of such automorphisms on the linear part of the origin parameter of the universal curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_LevelModuliPackageAbs_exists_algEquiv_comp_eq_classify_act_of_problemAut_relabel_of_factorsThrough_rigidDataH1Pow.lean

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_ModularCurve_WeierstrassGamma1Pow
import Definitions.Def_ModularCurve_WeierstrassH1Pow
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_LevelRelabelling

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel IsLocalRing FormalGroup

open scoped MatrixGroups

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance 10000] SubalgebraClass.toAlgebra
attribute [local instance 10001] AdicCompletion.instAlgebra

theorem ModularCurve.LevelModuliPackageAbs.exists_algEquiv_comp_eq_classify_act_of_problemAut_relabel_of_factorsThrough_rigidDataH1Pow
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M']

    (ℓg : ℕ) (hℓg : ℓg.Prime) (hℓg12 : ℓg % 12 = 11) (hℓgM' : ℓg ∣ M')
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

    (hℓA : IsUnit ((ℓg : ℕ) : A₀))
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
    (P₀ : LevelModuliPackageAbs A₀ (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum)

    (x : (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).Raw P₀.B₀)
    (hx : (Quot.mk _ x : (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).Pt P₀.B₀) = P₀.univ)

    (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R]

    [IsDomain R]
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

    (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M')
    (ργ : (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum.ProblemAut)
    (hpin : ∀ (T : Type) [Field T] [DecidableEq T] [Algebra A₀ T]
        (y y' : (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).Raw T) (hΔ : IsUnit y.level.2.2.curve.Δ),
        y'.curve = y.curve →
        y'.level.1 = y.level.1 →
        ModularCurve.LevelRelabelling.toPoint ((y.curve).baseChange T) y'.level.2.1.xP y'.level.2.1.yP =
          (((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) 0 0) •
            ModularCurve.LevelRelabelling.toPoint ((y.curve).baseChange T) y.level.2.1.xP y.level.2.1.yP →
        y'.level.2.1.xQ = y'.level.2.1.xP → y'.level.2.1.yQ = y'.level.2.1.yP →
        y'.level.2.2 = ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel 𝒢 ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) y.level.2.2 hΔ →
        ργ.act (Quot.mk _ y) = Quot.mk _ y')
    (hfix : ∀ b : P₀.B₀, ι (P₀.classify (ργ.act P₀.univ) b) - ι b ∈ maximalIdeal R) :
    ∃ θ₀ : R ≃ₐ[W₀] R,

      (∀ b : P₀.B₀, θ₀ (ι b) = ι (P₀.classify (ργ.act P₀.univ) b)) ∧

      (∀ r : R, θ₀ r - r ∈ maximalIdeal R) := by sorry
