-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_pt_restrictScalars_jOf_eq_classify_comp_eq_rigidDataH1Pow_of_isPrimitiveRoot_mul_of_dvd
-- name    : ModularCurve.FullLevel.exists_pt_restrictScalars_jOf_eq_classify_comp_eq_rigidDataH1Pow_of_isPrimitiveRoot_mul_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:35.562543+00:00
-- url     : https://prove2.me/theorems/3b251c03-6afe-5099-aa1a-7d4dcc9c1e11
-- title:
--   Lifting full-level points along a scalar restriction
-- statement:
--   Let $A_0$ be a commutative ring, $A$ an $A_0$-algebra, and $q,\ell,N$ natural numbers. Assume, over $A_0$ and again over $A$, three variable-change stability hypotheses: that `IsGamma1Point` for $\ell$ is preserved when a Weierstrass curve $W$ and level-$P$ data $D=(x_P,y_P,x_Q,y_Q)$ are transformed by $C$; that `IsGamma0PowAt` for $(p,k)$ is preserved when $h$ is replaced by `kernelVariableChangeDeg C (gamma0PowDeg p k) h`; and that divisibility of `inLineMulPoly W ℓ n x` by $h$ is preserved under the corresponding transformation. Let $\mathcal G_0$ be group laws over $A_0$ and $\mathcal T_0$ a level transport at $q$, giving the rigid datum `rigidDataH1Pow` over $A_0$ and, after restriction of scalars, over $A$; its raw objects over $T$ are a curve $W$ with $\Delta_W$ a unit, polynomials $h_p$ ($p\mid N$) generating cyclic $p^{v_p(N)}$-kernels, level-$P$ data which is a $\Gamma_1(\ell)$-point, a raw Drinfeld pair of level $q$, and the link condition $h_\ell \mid$ `inLineMulPoly W ℓ (ℓ^(v_ℓ(N)-1)) x_P`; points are raw objects modulo variable change, with $j$ the $j$-invariant. Let $P_0$, $P$ be abstract moduli packages for the two data, and $\varphi : P_0.B_0 \to P.B_0$ a ring map such that for every $A$-algebra $T$ and every raw object over $T$ the $A$-classifying map followed by $\varphi$ equals the $A_0$-classifying map. Then for every $A$-algebra $T$, viewed as an $A_0$-algebra through $A_0 \to A \to T$, every point $x$ of the $A_0$-datum over $T$ admits a point $x'$ of the $A$-datum over $T$ with $j(x')=j(x)$ and $(P.\mathrm{classify}\,x')\circ\varphi = P_0.\mathrm{classify}\,x$.
--
--   This is the point-level descent compatibility for the $\Gamma_1(\ell)$-guarded full-level moduli datum: points over an $A$-algebra computed relative to the base $A_0$ are matched, $j$-invariant and classifying homomorphism included, by points computed relative to $A$. It feeds the subsequent analysis of the classifying maps on charts and of minimal primes of the full-level ring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_pt_restrictScalars_jOf_eq_classify_comp_eq_rigidDataH1Pow_of_isPrimitiveRoot_mul_of_dvd.lean

import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctorRestrict
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_ModularCurve_WeierstrassGamma1Pow
import Definitions.Def_ModularCurve_WeierstrassH1Pow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal ModularCurve

theorem ModularCurve.FullLevel.exists_pt_restrictScalars_jOf_eq_classify_comp_eq_rigidDataH1Pow_of_isPrimitiveRoot_mul_of_dvd
    (A₀ : Type u) [CommRing A₀] (A : Type u) [CommRing A] [Algebra A₀ A] (q ℓ N : ℕ)
    (hℓ₀ : ∀ (T : Type u) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsGamma1Point W ℓ D →
        ModularCurve.IsGamma1Point (C • W) ℓ (D.variableChange C))
    (hM₀ : ∀ (T : Type u) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (hL₀ : ∀ (T : Type u) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (d n : ℕ) (h : Polynomial T) (x : T), h ∣ ModularCurve.inLineMulPoly W ℓ n x →
        ModularCurve.kernelVariableChangeDeg C d h ∣
          ModularCurve.inLineMulPoly (C • W) ℓ n (((C.u⁻¹ : Tˣ) : T) ^ 2 * (x - C.r)))
    (hℓ : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsGamma1Point W ℓ D →
        ModularCurve.IsGamma1Point (C • W) ℓ (D.variableChange C))
    (hM : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (hL : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (d n : ℕ) (h : Polynomial T) (x : T), h ∣ ModularCurve.inLineMulPoly W ℓ n x →
        ModularCurve.kernelVariableChangeDeg C d h ∣
          ModularCurve.inLineMulPoly (C • W) ℓ n (((C.u⁻¹ : Tˣ) : T) ^ 2 * (x - C.r)))
    (𝒢₀ : GroupLaws A₀) (𝒯₀ : LevelTransport A₀ 𝒢₀ q)
    (P₀ : LevelModuliPackageAbs A₀ (rigidDataH1Pow A₀ ℓ N q hℓ₀ hM₀ hL₀ 𝒢₀ 𝒯₀).toLevelModuliDatum)
    (P : LevelModuliPackageAbs A
      (rigidDataH1Pow A ℓ N q hℓ hM hL (𝒢₀.restrictScalars A) (𝒯₀.restrictScalars A)).toLevelModuliDatum)
    (φ : P₀.B₀ →+* P.B₀)

    (hφ : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (hΔ : IsUnit W.Δ)
          (h : ↥N.primeFactors → Polynomial T) (D : ModularCurve.LevelPData T) (z : RawDrinfeldPair T)
          (hh : ∀ p : ↥N.primeFactors, ModularCurve.IsGamma0PowAt W (p : ℕ) (N.factorization (p : ℕ)) (h p)) (hD : ModularCurve.IsGamma1Point W ℓ D)
          (hz : RawDrinfeldPair.IsLevel (𝒢₀.restrictScalars A) q W z) (hlk : ModularCurve.IsGamma1Link W ℓ N h D),
          letI : Algebra A₀ T := algebraRestrict A₀ A T
          (P.classify (Quot.mk _ (⟨W, hΔ, ⟨h, D, z⟩, ⟨⟨hh, hD, hz⟩, hlk⟩⟩ :
              (((gamma0PowComponent A N hM).prod ((gamma1Component A ℓ hℓ).prod
                (levelComponent A (𝒢₀.restrictScalars A) q (𝒯₀.restrictScalars A)))).restrict
                (fun W x => ModularCurve.IsGamma1Link W ℓ N x.1 x.2.1)
                (fun f _ _ _ hx => ModularCurve.IsGamma1Link.map f.toRingHom hx)
                (fun C W _ _ hx => fun hmem => hL _ W C _ _ _ _ (hx hmem))).Raw T))).toRingHom.comp φ =
          (P₀.classify (Quot.mk _ (⟨W, hΔ, ⟨h, D, z⟩, ⟨⟨hh, hD, hz⟩, hlk⟩⟩ :
              (((gamma0PowComponent A₀ N hM₀).prod ((gamma1Component A₀ ℓ hℓ₀).prod
                (levelComponent A₀ 𝒢₀ q 𝒯₀))).restrict
                (fun W x => ModularCurve.IsGamma1Link W ℓ N x.1 x.2.1)
                (fun f _ _ _ hx => ModularCurve.IsGamma1Link.map f.toRingHom hx)
                (fun C W _ _ hx => fun hmem => hL₀ _ W C _ _ _ _ (hx hmem))).Raw T))).toRingHom)
    (T : Type u) [CommRing T] [Algebra A T] :
    letI : Algebra A₀ T := algebraRestrict A₀ A T
    ∀ x : (rigidDataH1Pow A₀ ℓ N q hℓ₀ hM₀ hL₀ 𝒢₀ 𝒯₀).toLevelModuliDatum.Pt T,
      ∃ x' : (rigidDataH1Pow A ℓ N q hℓ hM hL (𝒢₀.restrictScalars A) (𝒯₀.restrictScalars A)).toLevelModuliDatum.Pt T,
        (rigidDataH1Pow A ℓ N q hℓ hM hL (𝒢₀.restrictScalars A) (𝒯₀.restrictScalars A)).toLevelModuliDatum.jOf x' =
          (rigidDataH1Pow A₀ ℓ N q hℓ₀ hM₀ hL₀ 𝒢₀ 𝒯₀).toLevelModuliDatum.jOf x ∧
        (P.classify x').toRingHom.comp φ = (P₀.classify x).toRingHom := by sorry
