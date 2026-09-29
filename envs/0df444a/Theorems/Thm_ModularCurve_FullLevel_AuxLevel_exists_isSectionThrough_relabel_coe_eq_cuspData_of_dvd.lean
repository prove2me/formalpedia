-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_AuxLevel_exists_isSectionThrough_relabel_coe_eq_cuspData_of_dvd
-- name    : ModularCurve.FullLevel.AuxLevel.exists_isSectionThrough_relabel_coe_eq_cuspData_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:22.181174+00:00
-- url     : https://prove2.me/theorems/52b79851-9897-5f8b-b285-5c3ea04f4786
-- title:
--   Relabelled Drinfeld pair passes through explicit cusp points
-- statement:
--   Fix a prime $q\ge 5$, a nonzero $M'$ with $q\nmid M'$, a prime $\ell\ge 3$ with $\ell\ne q$ and $\ell\nmid M'$, a field $L$ of characteristic zero that is a cyclotomic extension of $\mathbb{Q}$ of order $q\ell$, a primitive $q$-th root of unity $\zeta\in L$ and a primitive $q\ell$-th root $\xi\in L$. Let $K$ be the intermediate field of $L\subseteq L((\mathsf q))$ obtained by adjoining to $L$ the image under coefficientwise extension $\mathbb{Q}\to L$ of the $q$-expansion function field [`ModularCurve.xHFunctionField`](def/ModularCurve_XH.html#L79) of level $(q\ell)^2M'$ for the subgroup [`ModularCurve.FullLevel.levelH (q * ℓ) M'`](def/ModularCurve_FullLevelJacobian.html#L22), the kernel of the reduction $(\mathbb{Z}/(q\ell)^2M')^\times\to(\mathbb{Z}/q\ell)^\times$. Let $A$ be a discrete valuation domain with fraction field $L$, with $q$ in its maximal ideal, with $\zeta$ in the image of $A$, acting on $K$ compatibly, and let $\varpi$ generate its maximal ideal; let $j\in K$ be nonzero with image the $q$-expansion of the $j$-invariant. Assume: the stability of level-$\ell$ Katz structures [`ModularCurve.IsLevelPStructure`](def/ModularCurve_KatzLevelP.html#L104) under variable change, the stability of [`ModularCurve.IsGamma0PowAt`](def/ModularCurve_WeierstrassGamma0Pow.html#L55) under [`ModularCurve.kernelVariableChangeDeg`](def/ModularCurve_WeierstrassLevelComponents.html#L104), group laws $\mathcal{G}$ over $A$ that are chord–tangent and origin-identity, a section-transporting level transport $\mathcal{T}$ for $\mathcal{G}$ and $q$, and the existence of graded homomorphisms of projective-model rings realising variable changes and coefficient maps with the stated condition on irrelevant ideals (summarised here). Let $C$ be a variable change over $L((\mathsf q))$ and $r$ a raw point over $K$ of `rigidDataPow A ℓ M' q …`, consisting of a Weierstrass curve with unit discriminant, a tuple of $\Gamma_0$-type kernel polynomials indexed by the prime factors of $M'$, a level-$\ell$ Katz datum and a Drinfeld pair for $\mathcal{G}$ and $q$. The hypothesis `hr` pins $r$ at the Tate point: $C$ satisfies $u\,(2x+\tfrac16)=2y+x$ for the cusp point of index $(1,0)$ and has $r=-\tfrac1{12}$, $s=-\tfrac12$, $t=\tfrac1{24}$; the curve of $r$ maps to $C\bullet$[`ModularCurve.tateBase L (q * ℓ)`](def/ModularCurve_TateSlots.html#L46); for every prime $p\mid M'$ and every field $F'$ with a ring map $f:L\to F'$ and a primitive $p^{v_p(M')}$-th root of unity, the corresponding polynomial of $r$ becomes the variable-change transform of $\prod_a (X-x(\text{toric point at }\zeta^a))$ over $1\le a\le p^{v_p(M')}/2$ with $p\nmid a$; the level-$\ell$ datum of $r$ maps to [`ModularCurve.cuspData`](def/ModularCurve_KatzLevelPCusps.html#L71) at indices $(q,0)$, $(0,-q)$ twisted by $C$; and the two sections of the Drinfeld pair of $r$ pass through points of $K$ whose images are the $xP,yP$ and $xQ,yQ$ of [`ModularCurve.cuspData`](def/ModularCurve_KatzLevelPCusps.html#L71) at indices $(\ell,0)$, $(0,-\ell)$ twisted by $C$. Finally let $\gamma\in\mathrm{SL}_2(\mathbb{Z})$ lie in $\Gamma_0(M')$ with $q\mid\gamma_{00}$, and let $h_\Delta$ witness that the discriminant of the curve of the Drinfeld pair is a unit. The conclusion: there are $a,b,a',b'\in K$ such that the relabelled pair `RawDrinfeldPair.relabel`, whose two sections are the $\mathcal{G}$-linear combinations $\gamma_{00}P+\gamma_{10}Q$ and $\gamma_{01}P+\gamma_{11}Q$, has its first section passing through $(a,b)$ and its second through $(a',b')$ (each via a ring homomorphism from the $z$-chart ring carrying the affine coordinates to the given values), and moreover the images of $a$ and $b$ in $L((\mathsf q))$ are the $xP$ and $yP$ of [`ModularCurve.cuspData L (q * ℓ)`](def/ModularCurve_KatzLevelPCusps.html#L71) at the indices $(0,-\gamma_{10}\ell)$ and $(\gamma_{01}\ell,-\gamma_{11}\ell)$, twisted by $C$. No further identification of $a'$ and $b'$ is asserted.
--
--   This is the relabelling step in the analysis of the pinned Tate representative on the full-level modular curve: since the Tate parametrisation is a group homomorphism and $q\mid\gamma_{00}$, the combination $\gamma_{00}P+\gamma_{10}Q$ of the cusp points of indices $(\ell,0)$ and $(0,-\ell)$ is again a cusp point, of index $(0,-\gamma_{10}\ell)$ in $(\mathbb{Z}/q\ell)^2$. It feeds the construction of level automorphisms at the pinned point, being cited by [`ModularCurve.FullLevel.AuxLevel.exists_isLevelAutAt_mem_chartAlgFin_coe_eq_slotSubst_sub_and_apply_eq_laurent`](thm.html#ModularCurve.FullLevel.AuxLevel.exists_isLevelAutAt_mem_chartAlgFin_coe_eq_slotSubst_sub_and_apply_eq_laurent).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_AuxLevel_exists_isSectionThrough_relabel_coe_eq_cuspData_of_dvd.lean

import Mathlib
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_ModularCurve_LevelRelabelling
import Definitions.Def_ModularCurve_KatzLevelPCusps
import Definitions.Def_WeierstrassCurve_PointChart

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel

open scoped MatrixGroups

theorem ModularCurve.FullLevel.AuxLevel.exists_isSectionThrough_relabel_coe_eq_cuspData_of_dvd
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {q * ℓ} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ q)
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ))
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M')
        (ModularCurve.FullLevel.levelH (q * ℓ) M')))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ x : A, algebraMap A L x = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})

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

    (C : WeierstrassCurve.VariableChange (LaurentSeries L)) (r : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).Raw ↥K)
    (hr : haveI : NeZero (q * ℓ) := ⟨Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero⟩

      (((C.u : (LaurentSeries L)ˣ) : LaurentSeries L) * (2 * (ModularCurve.cuspPoint L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![1, 0]).1 + HahnSeries.C ((6 : L)⁻¹)) =
          2 * (ModularCurve.cuspPoint L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![1, 0]).2 + (ModularCurve.cuspPoint L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![1, 0]).1 ∧
        C.r = HahnSeries.C (-(12 : L)⁻¹) ∧ C.s = HahnSeries.C (-(2 : L)⁻¹) ∧ C.t = HahnSeries.C ((24 : L)⁻¹)) ∧

      r.curve.map (algebraMap ↥K (LaurentSeries L)) = C • ModularCurve.tateBase L (q * ℓ) ∧

      (∀ (p : ↥M'.primeFactors) (F' : Type) [Field F'] (f : L →+* F') (ζ : F'),
        IsPrimitiveRoot ζ ((p : ℕ) ^ M'.factorization (p : ℕ)) →
        ((r.level.1 p).map (algebraMap ↥K (LaurentSeries L))).map (ModularCurve.coeffMap f) =
          ModularCurve.kernelVariableChangeDeg (C.map (ModularCurve.coeffMap f))
            (ModularCurve.gamma0PowDeg (p : ℕ) (M'.factorization (p : ℕ)))
            (∏ a ∈ (Finset.Icc 1 ((p : ℕ) ^ M'.factorization (p : ℕ) / 2)).filter (fun a => ¬ (p : ℕ) ∣ a),
              (Polynomial.X - Polynomial.C (ModularCurve.toricPoint F' (q * ℓ) (ζ ^ a)).1))) ∧

      r.level.2.1.map (algebraMap ↥K (LaurentSeries L)) = (ModularCurve.cuspData L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![(q : ZMod (q * ℓ)), 0] ![0, -(q : ZMod (q * ℓ))]).variableChange C ∧

      (∃ Px Py Qx Qy : ↥K,
        (Px : LaurentSeries L) = ((ModularCurve.cuspData L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![(ℓ : ZMod (q * ℓ)), 0] ![0, -(ℓ : ZMod (q * ℓ))]).variableChange C).xP ∧
        (Py : LaurentSeries L) = ((ModularCurve.cuspData L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![(ℓ : ZMod (q * ℓ)), 0] ![0, -(ℓ : ZMod (q * ℓ))]).variableChange C).yP ∧
        (Qx : LaurentSeries L) = ((ModularCurve.cuspData L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![(ℓ : ZMod (q * ℓ)), 0] ![0, -(ℓ : ZMod (q * ℓ))]).variableChange C).xQ ∧
        (Qy : LaurentSeries L) = ((ModularCurve.cuspData L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![(ℓ : ZMod (q * ℓ)), 0] ![0, -(ℓ : ZMod (q * ℓ))]).variableChange C).yQ ∧
        IsSectionThrough r.level.2.2.P Px Py ∧ IsSectionThrough r.level.2.2.Q Qx Qy))

    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M') (hγq : (q : ℤ) ∣ (γ 0 0 : ℤ))
    (hΔ : IsUnit r.level.2.2.curve.Δ) :
    haveI : NeZero (q * ℓ) := ⟨Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero⟩
    ∃ a b a' b' : ↥K,
      IsSectionThrough (ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel 𝒢
        ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) r.level.2.2 hΔ).P a b ∧
      IsSectionThrough (ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel 𝒢
        ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) r.level.2.2 hΔ).Q a' b' ∧
      (a : LaurentSeries L) = ((ModularCurve.cuspData L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit
        ![0, -(((γ 1 0 : ℤ) : ZMod (q * ℓ)) * ℓ)] ![((γ 0 1 : ℤ) : ZMod (q * ℓ)) * ℓ, -(((γ 1 1 : ℤ) : ZMod (q * ℓ)) * ℓ)]).variableChange C).xP ∧
      (b : LaurentSeries L) = ((ModularCurve.cuspData L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit
        ![0, -(((γ 1 0 : ℤ) : ZMod (q * ℓ)) * ℓ)] ![((γ 0 1 : ℤ) : ZMod (q * ℓ)) * ℓ, -(((γ 1 1 : ℤ) : ZMod (q * ℓ)) * ℓ)]).variableChange C).yP := by sorry
