-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_Diamond_exists_levelReading_baseChange_of_isAlgClosed_rigidDataH1Pow
-- name    : ModularCurve.FullLevel.Diamond.exists_levelReading_baseChange_of_isAlgClosed_rigidDataH1Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:30.533368+00:00
-- url     : https://prove2.me/theorems/b21617c6-d3b8-5b92-844a-ffe628a158ca
-- title:
--   Reading H₁-level structures over an algebraically closed field
-- statement:
--   Fix a prime $q$, a natural number $M'\neq 0$, a prime $\ell_g\ge 3$ with $\ell_g\mid M'$, and a commutative ring $A$. Three stability hypotheses are assumed, for all $A$-algebras $T$, Weierstrass curves over $T$ and variable changes $C$: `hℓ`, that [`ModularCurve.IsGamma1Point`](def/ModularCurve_WeierstrassGamma1Pow.html#L10) for $\ell_g$ (the pair $(x_P,y_P)$ satisfies the affine equation, $\mathrm{pre}\Psi_{\ell_g}$ vanishes at $x_P$, and $(x_Q,y_Q)=(x_P,y_P)$) is preserved by `LevelPData.variableChange`; `hM`, that [`ModularCurve.IsGamma0PowAt`](def/ModularCurve_WeierstrassGamma0Pow.html#L55) (a two-torsion kernel generator when $p^k=2$, otherwise a normalised cyclic kernel generator of degree at most $\varphi(p^k)/2$ dividing $\mathrm{pre}\Psi_{p^k}$ appropriately) is preserved by [`ModularCurve.kernelVariableChangeDeg`](def/ModularCurve_WeierstrassLevelComponents.html#L104); and `hL`, that divisibility of [`ModularCurve.inLineMulPoly`](def/ModularCurve_WeierstrassH1Pow.html#L18) is preserved under the same substitution. Further data: group laws $\mathcal G$ on the projective models of discriminant-unit Weierstrass curves over $A$-algebras, chord-tangent and with identity at the origin chart; a level transport $\mathcal T$ for $\Gamma(q)$-Drinfeld pairs satisfying `IsSectionTransport`; and `hVC`, `hCO`, providing graded ring homomorphisms realising variable changes and coefficient changes on projective models. Finally, $\Omega$ is an algebraically closed $A$-algebra field of characteristic zero, $K_0$ a field between $A$ and $\Omega$ in a scalar tower, and $E$ an elliptic Weierstrass curve over $K_0$. Let $L$ be the level component obtained from the product of the $\Gamma_0$-power component for $M'$, the $\Gamma_1(\ell_g)$ component and the Drinfeld $\Gamma(q)$ component, restricted by [`ModularCurve.IsGamma1Link`](def/ModularCurve_WeierstrassH1Pow.html#L26) (the $\ell_g$-th kernel polynomial divides `inLineMulPoly` at $x_P$). The assertion: there is a map $\Theta$ from $L.\mathrm{obj}\,\Omega$ to triples-plus-subgroup $((P,(P_1,P_2)),C)$ in $E_\Omega(\Omega)^3\times$ subgroups of $E_\Omega(\Omega)$ such that for every $\beta$ which is an $L$-level structure on $E_{\Omega}$: $\ell_g P=0$, $P\neq 0$ and $P\in C$; $qP_1=qP_2=0$ and every integral relation $aP_1+bP_2=0$ has $q\mid a$, $q\mid b$; $C$ is cyclic of order $M'$; and for every $\sigma\in\mathrm{Aut}(\Omega/K_0)$, $\Theta$ of the image of $\beta$ under the functorial map along $\sigma$ equals the componentwise image of $\Theta(\beta)$ under $\sigma$ applied to points, with $C$ replaced by its image.
--
--   This is the dictionary translating level structures for the link-restricted rigid $H_1$ moduli problem ($\Gamma_0(M')$ kernel polynomials, a $\Gamma_1(\ell_g)$ point lying on the cyclic subgroup, and a $\Gamma(q)$ Drinfeld basis) over an algebraically closed field of characteristic zero into classical torsion data on the base-changed elliptic curve, together with equivariance for $\mathrm{Aut}(\Omega/K_0)$. It is used in the degree estimate [`ModularCurve.FullLevel.Diamond.index_le_finrank_adjoin_jOf_of_transcendental_jOf_rigidDataH1Pow`](thm.html#ModularCurve.FullLevel.Diamond.index_le_finrank_adjoin_jOf_of_transcendental_jOf_rigidDataH1Pow), where counting level structures on a curve with transcendental $j$-invariant requires this classical description.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_Diamond_exists_levelReading_baseChange_of_isAlgClosed_rigidDataH1Pow.lean

import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_ModularCurve_WeierstrassGamma1Pow
import Definitions.Def_ModularCurve_WeierstrassH1Pow
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel

universe u

theorem ModularCurve.FullLevel.Diamond.exists_levelReading_baseChange_of_isAlgClosed_rigidDataH1Pow
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (ℓg : ℕ) (hℓg : ℓg.Prime) (hℓg3 : 3 ≤ ℓg) (hℓgM' : ℓg ∣ M')
    (A : Type u) [CommRing A]

    (hℓ : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsGamma1Point W ℓg D →
        ModularCurve.IsGamma1Point (C • W) ℓg (D.variableChange C))
    (hM : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (hL : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (d n : ℕ) (h : Polynomial T) (x : T), h ∣ ModularCurve.inLineMulPoly W ℓg n x →
        ModularCurve.kernelVariableChangeDeg C d h ∣
          ModularCurve.inLineMulPoly (C • W) ℓg n (((C.u⁻¹ : Tˣ) : T) ^ 2 * (x - C.r)))
    (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (𝒯 : LevelTransport A 𝒢 q) (h𝒯 : 𝒯.IsSectionTransport)
    (hVC : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve.Projective T) (C : WeierstrassCurve.VariableChange T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (C • W))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • W)) ≤ (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsVariableChangeHom W C φ)
    (hCO : ∀ (T T' : Type u) [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T')
      (W : WeierstrassCurve.Projective T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f.toRingHom))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f.toRingHom)) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsCoefficientHom W f.toRingHom φ)

    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [CharZero Ω] [DecidableEq Ω] [Algebra A Ω]
    (K₀ : Type u) [Field K₀] [Algebra A K₀] [Algebra K₀ Ω] [IsScalarTower A K₀ Ω]
    (E : WeierstrassCurve K₀) [E.IsElliptic] :
    ∃ Θ : ((((ModularCurve.gamma0PowComponent A M' hM).prod
        ((ModularCurve.gamma1Component A ℓg hℓ).prod (WeierstrassCurve.DrinfeldGlobal.levelComponent A 𝒢 q 𝒯))).restrict
        (fun W x => ModularCurve.IsGamma1Link W ℓg M' x.1 x.2.1)
        (fun f _ _ _ hx => ModularCurve.IsGamma1Link.map f.toRingHom hx)
        (fun C W _ _ hx => fun hmem => hL _ W C _ _ _ _ (hx hmem)))).obj Ω →
        ((E.baseChange Ω).toAffine.Point ×
          ((E.baseChange Ω).toAffine.Point × (E.baseChange Ω).toAffine.Point)) ×
          AddSubgroup (E.baseChange Ω).toAffine.Point,
      ∀ β : ((((ModularCurve.gamma0PowComponent A M' hM).prod
        ((ModularCurve.gamma1Component A ℓg hℓ).prod (WeierstrassCurve.DrinfeldGlobal.levelComponent A 𝒢 q 𝒯))).restrict
        (fun W x => ModularCurve.IsGamma1Link W ℓg M' x.1 x.2.1)
        (fun f _ _ _ hx => ModularCurve.IsGamma1Link.map f.toRingHom hx)
        (fun C W _ _ hx => fun hmem => hL _ W C _ _ _ _ (hx hmem)))).obj Ω,
        ((((ModularCurve.gamma0PowComponent A M' hM).prod
        ((ModularCurve.gamma1Component A ℓg hℓ).prod (WeierstrassCurve.DrinfeldGlobal.levelComponent A 𝒢 q 𝒯))).restrict
        (fun W x => ModularCurve.IsGamma1Link W ℓg M' x.1 x.2.1)
        (fun f _ _ _ hx => ModularCurve.IsGamma1Link.map f.toRingHom hx)
        (fun C W _ _ hx => fun hmem => hL _ W C _ _ _ _ (hx hmem)))).IsLevel (E.baseChange Ω) β →

        (ℓg • (Θ β).1.1 = 0 ∧ (Θ β).1.1 ≠ 0 ∧ (Θ β).1.1 ∈ (Θ β).2) ∧

        (q • (Θ β).1.2.1 = 0 ∧ q • (Θ β).1.2.2 = 0 ∧
          ∀ a b : ℤ, a • (Θ β).1.2.1 + b • (Θ β).1.2.2 = 0 → (q : ℤ) ∣ a ∧ (q : ℤ) ∣ b) ∧

        (IsAddCyclic (Θ β).2 ∧ Nat.card (Θ β).2 = M') ∧

        (∀ σ : Ω ≃ₐ[K₀] Ω,
          Θ (((((ModularCurve.gamma0PowComponent A M' hM).prod
        ((ModularCurve.gamma1Component A ℓg hℓ).prod (WeierstrassCurve.DrinfeldGlobal.levelComponent A 𝒢 q 𝒯))).restrict
        (fun W x => ModularCurve.IsGamma1Link W ℓg M' x.1 x.2.1)
        (fun f _ _ _ hx => ModularCurve.IsGamma1Link.map f.toRingHom hx)
        (fun C W _ _ hx => fun hmem => hL _ W C _ _ _ _ (hx hmem)))).map
              ((σ : Ω →ₐ[K₀] Ω).restrictScalars A) β) =
            ((WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[K₀] Ω) (Θ β).1.1,
              (WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[K₀] Ω) (Θ β).1.2.1,
                WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[K₀] Ω) (Θ β).1.2.2)),
              ((Θ β).2).map (WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[K₀] Ω)))) := by sorry
