-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_exists_verticalUnit_atkinLehner_eq_mul_inv_residue_eq_prod_ssJSet_of_prolongationDatum_offDiag_of_wgen
-- name    : ModularCurve.XHDRModelAtP.exists_verticalUnit_atkinLehner_eq_mul_inv_residue_eq_prod_ssJSet_of_prolongationDatum_offDiag_of_wgen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/f69be8ba-ef19-5f40-ac11-911a6b4b2b67
-- title:
--   Existence of Ogg's vertical unit with Atkin–Lehner relation
-- statement:
--   Fix a prime $p$ and $M$ with $p \mid M$, $p^{2} \nmid M$, a subgroup $H \le (\mathbb{Z}/M)^{\times}$ containing every unit whose image in $(\mathbb{Z}/(M/p))^{\times}$ is $1$, and the hypothesis $hj$ that the series `jqModC ℚ` lies in `qExpFunctionFieldC ℚ ⊤`; fix a model datum $\mathfrak{X} :$ `XHDRModelAtP p M H hpM hj` (an integral model of $X_H(M)$ over $R_p$ carrying a curve model $\mathfrak{X}.\mathrm{Meta}$ of $F_M = \overline{\mathbb{Q}}\cdot F(\Gamma_H(M))$, its identification $\mathfrak{X}.\mathrm{eeta}$ with the geometric generic fibre, and an Atkin–Lehner isomorphism $\mathfrak{X}.w$). Fix further: a valuation subring $A \subset \overline{\mathbb{Q}}$ with $p$ a non-unit of $A$ and residue field $\kappa$ algebraically closed of characteristic $p$; a ring map $\rho : R_p \to A$ whose composite with $A \hookrightarrow \overline{\mathbb{Q}}$ is the structure map; a unit $pb$ of $\mathbb{Z}/(M/p)$ with underlying element $p$, and the self-map $\delta$ of places of $\bar F =$ `Fbar p M H hpM κ` given by the diamond automorphism of the $\Gamma_0(M/p)$-lift of $pb$; a finset $SS$ of pairs of places whose members are exactly the pairs $(\,\mathrm{Frob}_p(v), v)$ with $v$ supersingular; an automorphism $\theta$ of $F_M$ over $\overline{\mathbb{Q}}$ commuting with the arithmetic Galois action, and an integral $\overline{\mathbb{Q}}$-algebra map $\alpha$ from $F_{M/p} = \overline{\mathbb{Q}}\cdot F(\Gamma_{H'}(M/p))$ to $F_M$ with $\theta \circ \alpha$ integral, $\alpha$ preserving $q$-expansions and $\theta \circ \alpha$ sending a $q$-expansion to its image under $q \mapsto q^{p}$; a place-specialisation datum $Psp$ and a prolongation datum $Rpd$ for $\theta$, consisting of two regular prolongations $R_1, R_2$ of $A$ in $F_M$ with residue fields in $\bar F$, related by $f \in R_2 \iff \theta f \in R_1$. Assumed in addition: $hwgen$, that $\theta$ induces the Atkin–Lehner transport on places of $\mathfrak{X}.\mathrm{Meta}$ through $\mathfrak{X}.w$; the type dichotomy, model, order, regularity and node-value laws for $Rpd$ relative to $\alpha$, $\theta\circ\alpha$, $\delta$ and $SS$; and two compatibilities $hcompat$, $hcompat'$ between the places of the special fibre of the model and the reductions `reduceFst`, `reduceSnd` together with the mod-$p$ Frobenius on places (summarised here). The conclusion asserts the existence of $G \in F_M$, an $m \in \mathbb{N}$, a $c \in \overline{\mathbb{Q}}$, a finite $S_0 \subset \kappa$, multiplicities $n : \kappa \to \mathbb{N}$ and $e \in \kappa$, with $G$ in the valuation ring $Rpd.R_1.\mathrm{integers}$, such that: $c \neq 0$ and $A$-valuation of $c$ is $< 1$; $e \neq 0$, every $a \in S_0$ lies in `ssJSet p κ` (those $j \in \kappa$ for which each elliptic Weierstrass curve over $\kappa$ with invariant $j$ has no non-trivial $p$-torsion point), $\sum_{a \in S_0} n(a) = m$, and for every $xb \in \bar F$ with $q$-expansion `jqModC κ` the $R_1$-residue of $G$ equals $e \prod_{a \in S_0}(xb - a)^{n(a)}$; $\theta G = c \, G^{-1}$; $\mathrm{ord}_V(G) = 0$ at every place $V$ of $F_M$ that is not cuspidal (cuspidality of $V$ meaning $\mathrm{ord}_V(x - a) \le 0$ for every $x$ with $q$-expansion `jqModC` and every $a \in A$); $\mathrm{ord}_C(G) = m\,\mathrm{ord}_C(x)$ for every $x$ with $q$-expansion `jqModC` at every place $C$ on the $\infty$-side; and $\mathrm{ord}_C(G) = -m\,\mathrm{ord}_C(x')$ for every $x'$ with $q$-expansion the image of `jqModC` under $q \mapsto q^{p}$ at every place $C$ on the $0$-side.
--
--   This is the existence, in the present formal framework, of Ogg's vertical unit $\Delta(\tau)/\Delta(p\tau)$ on $X_H(M)$ at a prime exactly dividing the level: a function whose divisor is supported on the cusps, which is exchanged with a constant multiple of its inverse by the Atkin–Lehner involution, and whose reduction on the $\infty$-component of the Deligne–Rapoport fibre is a product of linear factors at supersingular $j$-invariants; here the degree $m$ and the constant $c$ are existentially quantified rather than identified with $p-1$ and $p^{12}$. It is used by [`ModularCurve.XHDRModelAtP.exists_residueCarrier_of_ne_zero_of_prolongationDatum_offDiag_of_wgen`](thm.html#ModularCurve.XHDRModelAtP.exists_residueCarrier_of_ne_zero_of_prolongationDatum_offDiag_of_wgen).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_exists_verticalUnit_atkinLehner_eq_mul_inv_residue_eq_prod_ssJSet_of_prolongationDatum_offDiag_of_wgen.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_ComponentGroup
import Definitions.Def_AlgebraicCurve_SemistableCharts

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve
  IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP
open scoped MatrixGroups

theorem ModularCurve.XHDRModelAtP.exists_verticalUnit_atkinLehner_eq_mul_inv_residue_eq_prod_ssJSet_of_prolongationDatum_offDiag_of_wgen
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
    :
    ∃ (G : ↥(xHFunctionFieldBar M H)) (m : ℕ) (c : AlgebraicClosure ℚ) (S₀ : Finset (ResidueField ↥A)) (n : ResidueField ↥A → ℕ) (e : ResidueField ↥A)
      (hG₁ : G ∈ Rpd.R₁.integers),

      (c ≠ 0 ∧ A.valuation c < 1) ∧

      (e ≠ 0 ∧ (∀ a ∈ S₀, a ∈ @ssJSet p (ResidueField ↥A) _ (Classical.decEq _)) ∧ (∑ a ∈ S₀, n a = m) ∧
        ∀ xb : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A), ((xb : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A)) = jqModC (ResidueField ↥A) →
          Rpd.R₁.residue ⟨G, hG₁⟩ =
            algebraMap (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) e * ∏ a ∈ S₀, (xb - algebraMap (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) a) ^ n a) ∧

      θ G = algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) c * G⁻¹ ∧

      (∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), ¬ JHPlaceSpecialization.IsCuspidal (M := M) (H := H) (A := A) V → V.ord G = 0) ∧

      (∀ x : ↥(xHFunctionFieldBar M H), ((x : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ) →
        ∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A) C → C.ord G = (m : ℤ) * C.ord x) ∧
      (∀ x' : ↥(xHFunctionFieldBar M H), ((x' : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (jqModC (AlgebraicClosure ℚ)) →
        ∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A) C → C.ord G = -((m : ℤ) * C.ord x')) := by sorry
