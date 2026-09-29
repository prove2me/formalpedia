-- Prove2me | Theorems.Thm_ModularCurve_LevelRelabelling_exists_problemAut_relabel_one_mul_of_isUnit_det_gamma0Pow
-- name    : ModularCurve.LevelRelabelling.exists_problemAut_relabel_one_mul_of_isUnit_det_gamma0Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/f65c9971-ba64-5fe4-8351-cf89534cd974
-- title:
--   Relabelling problem automorphisms for the Γ₀(M')×Γ(ℓ)×Γ(q) datum
-- statement:
--   Fix primes $q$ and $\ell$ with $\ell\ge 3$, a natural number $M'\neq 0$, and a commutative ring $A$ in which $\ell$ is invertible. Assume: $(hℓ)$ level-$\ell$ Katz data (four coordinates $x_P,y_P,x_Q,y_Q$ satisfying the curve equations, vanishing of $\mathrm{pre}\Psi_\ell$ and unit independence elements) remain such after a Weierstrass variable change, transported by `LevelPData.variableChange`; $(hM)$ the predicate `IsGamma0PowAt` for $p,k$ is preserved by variable change, transported by `kernelVariableChangeDeg`; $𝒢$ is a family of relative group laws on the projective models of discriminant-unit curves over $A$-algebras which is chord–tangent and has the origin as identity; $𝒯$ is a level-$q$ transport for $𝒢$ satisfying `IsSectionTransport`; and $(hVC)$, $(hCO)$ that every variable change, respectively every $A$-algebra map of coefficients, is realised by a graded ring homomorphism of the projective coordinate rings satisfying `IsVariableChangeHom`, respectively `IsCoefficientHom`, and carrying the irrelevant ideal appropriately. Then there is a map $\rho$ from $2\times 2$ integer matrices to automorphisms of the moduli problem attached to `rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯`, whose raw objects over a test $A$-algebra $T$ are a Weierstrass curve with unit discriminant together with a $\Gamma_0$-slot (a polynomial $h_p$ with `IsGamma0PowAt` for each prime $p\mid M'$ and exponent $v_p(M')$), a level-$\ell$ Katz slot and a Drinfeld level-$q$ slot (a curve with two sections forming a Drinfeld $q$-basis), points being variable-change classes of raw objects, and automorphisms acting naturally in $T$ and preserving $j$. The four asserted properties are: (i) for $g$ whose reduction mod $q\ell$ has unit determinant, for every field $T$ that is an $A$-algebra and raw objects $x,x'$ over $T$ with $x.level.2.2.curve$ of unit discriminant, if $x'$ has the same curve and the same $\Gamma_0$-slot as $x$, its level-$\ell$ slot is `LevelPData.relabel` of that of $x$ by $g$ (the pair of affine points replaced by $g_{00}P+g_{10}Q$ and $g_{01}P+g_{11}Q$) and its Drinfeld slot is `RawDrinfeldPair.relabel` of that of $x$ by $g$ (the two sections replaced by the corresponding $\mathbb Z$-linear combinations for $𝒢$), then $\rho(g)$ sends the class of $x$ to the class of $x'$; (ii) $\rho(1)$ acts as the identity on points over every test algebra; (iii) for $g,h$ with unit determinant mod $q\ell$, $\rho(gh)$ acts as $\rho(g)$ followed by $\rho(h)$; (iv) if $g$ has unit determinant mod $q\ell$ and $g\equiv g'$ mod $q\ell$, then $\rho(g)$ and $\rho(g')$ act identically.
--
--   This supplies the relabelling family through which $\mathrm{GL}_2(\mathbb Z/q\ell)$ acts on the right on the rigidified moduli problem with $\Gamma_0(M')$, full level $\ell$ and Drinfeld level $q$ structure, the classical action permuting level structures on a fixed curve. It is used by [`ModularCurve.LevelRelabelling.exists_isModuliRelabelling_gamma0Pow`](thm.html#ModularCurve.LevelRelabelling.exists_isModuliRelabelling_gamma0Pow), where the family is cut down to $\Gamma_0(M')$-type matrices and inverses are produced.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_LevelRelabelling_exists_problemAut_relabel_one_mul_of_isUnit_det_gamma0Pow.lean

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

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel

open scoped MatrixGroups

theorem ModularCurve.LevelRelabelling.exists_problemAut_relabel_one_mul_of_isUnit_det_gamma0Pow
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ)
    (A : Type) [CommRing A] (hℓA : IsUnit ((ℓ : ℕ) : A))
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
        IsCoefficientHom W f.toRingHom φ) :
    ∃ ρ : Matrix (Fin 2) (Fin 2) ℤ → (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.ProblemAut,

      (∀ (g : Matrix (Fin 2) (Fin 2) ℤ), IsUnit (g.map (Int.castRingHom (ZMod (q * ℓ)))).det →
        ∀ (T : Type) [Field T] [Algebra A T]
          (x x' : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).Raw T) (hΔ : IsUnit x.level.2.2.curve.Δ),
          x'.curve = x.curve →
          x'.level.1 = x.level.1 →
          x'.level.2.1 = ModularCurve.LevelRelabelling.LevelPData.relabel x.curve g x.level.2.1 →
          x'.level.2.2 = ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel 𝒢 g x.level.2.2 hΔ →
          (ρ g).act (Quot.mk _ x) = Quot.mk _ x') ∧

      (∀ (T : Type) [CommRing T] [Algebra A T] (y : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.Pt T),
        (ρ 1).act y = y) ∧

      (∀ (g h : Matrix (Fin 2) (Fin 2) ℤ), IsUnit (g.map (Int.castRingHom (ZMod (q * ℓ)))).det →
        IsUnit (h.map (Int.castRingHom (ZMod (q * ℓ)))).det →
        ∀ (T : Type) [CommRing T] [Algebra A T] (y : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.Pt T),
          (ρ (g * h)).act y = (ρ h).act ((ρ g).act y)) ∧

      (∀ (g g' : Matrix (Fin 2) (Fin 2) ℤ), IsUnit (g.map (Int.castRingHom (ZMod (q * ℓ)))).det →
        g.map (Int.castRingHom (ZMod (q * ℓ))) = g'.map (Int.castRingHom (ZMod (q * ℓ))) →
        ∀ (T : Type) [CommRing T] [Algebra A T] (y : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.Pt T),
          (ρ g).act y = (ρ g').act y) := by sorry
