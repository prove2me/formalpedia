-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_integers_ne_and_forall_valuationSubring_eq_or_eq_of_residue_eq_qExpFrobeniusModL
-- name    : ModularCurve.XHDRModelAtP.integers_ne_and_forall_valuationSubring_eq_or_eq_of_residue_eq_qExpFrobeniusModL
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/6edba900-2fe2-5dad-97f1-68684c1c5a9c
-- title:
--   Distinctness and exhaustiveness of the two prolongations at p ∥ M
-- statement:
--   Fix a prime $p$ and a nonzero level $M$ with $p \mid M$ but $p^2 \nmid M$, and a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit that reduces to $1$ in $(\mathbb{Z}/(M/p))^\times$, with $M/p \neq 0$; assume the $q$-expansion $j$ of the modular invariant lies in the rational $q$-expansion function field of $SL(2,\mathbb{Z})$, and let $\mathfrak{X}$ be an integral model datum `XHDRModelAtP` for level $(p,M,H)$, which in particular supplies a curve model $\mathfrak{X}.\mathrm{Meta}$ over $\overline{\mathbb{Q}}$ with function field $\bar F =$ `xHFunctionFieldBar M H` together with the morphism $\mathfrak{X}.w$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a nonunit of $A$ (`LiesOverPrime p`), whose residue field $\kappa$ is algebraically closed of characteristic $p$, and let $\rho : R_p \to A$ be a ring homomorphism lifting the structure map $R_p \to \overline{\mathbb{Q}}$. Let $\theta$ be an $\overline{\mathbb{Q}}$-algebra automorphism of $\bar F$, assumed (hypothesis `hwgen`) to induce on places the same action as $\mathfrak{X}.w$: for any two sections $y,y'$ of $\mathfrak{X}.\mathrm{Meta}.\mathrm{toBase}$ over $\operatorname{Spec}\overline{\mathbb{Q}}$ such that $y'$ followed by $\mathfrak{X}.\mathrm{eeta}$, the first pullback projection and $\mathfrak{X}.w.\mathrm{hom}$ equals $y$ followed by $\mathfrak{X}.\mathrm{eeta}$ and that projection, the place attached to $y'$ is the image of the place attached to $y$ under the semilinear automorphism $\theta$. Let $\alpha$ be an $\overline{\mathbb{Q}}$-algebra map from `xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)` to $\bar F$ which is the identity on underlying Laurent series. Let $\mathrm{Psp}$ be a place-specialisation datum `JHPlaceSpecialization p M H hpM A` and $\mathrm{Rpd}$ a prolongation datum for it relative to $\theta$, thus two regular prolongations $R_1, R_2$ of $A$ to $\bar F$ with values in the reduction field, with $f \in R_2$ iff $\theta f \in R_1$ and residues matched through $\theta$. Assume the Frobenius residue law: for every $v$ at level $M/p$ with $\alpha v$ in the integer rings of both $R_1$ and $R_2$, the $R_2$-residue of $\alpha v$ is the image of its $R_1$-residue under the $p$-power $q$-expansion Frobenius `qExpFrobeniusModL` over $\kappa$ at level $\Gamma_N(p,M,H)$. Finally let $x \in \bar F$ have Laurent series equal to $j$ over $\overline{\mathbb{Q}}$. The conclusion is threefold: the valuation rings $R_1.\mathrm{integers}$ and $R_2.\mathrm{integers}$ are distinct; every valuation subring $O$ of $\bar F$ whose intersection with $\overline{\mathbb{Q}}$ is exactly $A$ (i.e. $c \in A$ iff the image of $c$ lies in $O$) and for which $Q(x)$ and $Q(x)^{-1}$ both lie in $O$ for every polynomial $Q$ over $A$ with nonzero reduction modulo the maximal ideal of $A$ equals $R_1.\mathrm{integers}$ or $R_2.\mathrm{integers}$; and both $R_1.\mathrm{integers}$ and $R_2.\mathrm{integers}$ do have this last property, namely $Q(x)$ is a unit in each of them for every such $Q$.
--
--   This is the two-component statement for the fibre at a prime $p$ exactly dividing the level: the two prolongations of $A$ attached to the $q$-expansion at $\infty$ and to its $\theta$-twist are distinct, and together they exhaust the valuation rings of $\overline{\mathbb{Q}}$-function field of $X_H(M)$ that restrict to $A$ and are generic over the $j$-line, both being themselves of that kind. It feeds the construction of an element of the first prolongation whose residue is $j$ times an inverse power of the $q$-expansion Frobenius of $j$, used in the Deligne–Rapoport description of the reduction of $X_H(M)$ at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_integers_ne_and_forall_valuationSubring_eq_or_eq_of_residue_eq_qExpFrobeniusModL.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_ComponentGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve
  IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP
open scoped MatrixGroups

theorem ModularCurve.XHDRModelAtP.integers_ne_and_forall_valuationSubring_eq_or_eq_of_residue_eq_qExpFrobeniusModL
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)

    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)

    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))

    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)

    (hres₂α : ∀ (v : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) (h₁ : α v ∈ Rpd.R₁.integers) (h₂ : α v ∈ Rpd.R₂.integers),
      Rpd.R₂.residue ⟨α v, h₂⟩ = qExpFrobeniusModL (ResidueField ↥A) (ΓN p M H hpM) p (Rpd.R₁.residue ⟨α v, h₁⟩))

    (x : ↥(xHFunctionFieldBar M H)) (hx : ((x : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ)) :

    Rpd.R₁.integers ≠ Rpd.R₂.integers ∧

    (∀ O : ValuationSubring ↥(xHFunctionFieldBar M H),
      (∀ c : AlgebraicClosure ℚ, algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) c ∈ O ↔ c ∈ A) →
      (∀ Q : Polynomial ↥A, Q.map (IsLocalRing.residue ↥A) ≠ 0 →
        Polynomial.aeval x (Q.map A.subtype) ∈ O ∧ (Polynomial.aeval x (Q.map A.subtype))⁻¹ ∈ O) →
      O = Rpd.R₁.integers ∨ O = Rpd.R₂.integers) ∧

    (∀ Q : Polynomial ↥A, Q.map (IsLocalRing.residue ↥A) ≠ 0 →
      (Polynomial.aeval x (Q.map A.subtype) ∈ Rpd.R₁.integers ∧ (Polynomial.aeval x (Q.map A.subtype))⁻¹ ∈ Rpd.R₁.integers) ∧
      (Polynomial.aeval x (Q.map A.subtype) ∈ Rpd.R₂.integers ∧ (Polynomial.aeval x (Q.map A.subtype))⁻¹ ∈ Rpd.R₂.integers)) := by sorry
