-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_orderLawFixed_prolongationDatum_of_norm
-- name    : ModularCurve.XHDRModelAtP.orderLawFixed_prolongationDatum_of_norm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/40247613-8a3b-5e60-87a8-d0a568b9f51b
-- title:
--   Fixed-place order law from the reduced norm datum
-- statement:
--   Fix a prime $p$ and $M \neq 0$ with $p \mid M$ but $p^2 \nmid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit that becomes $1$ in $(\mathbb{Z}/(M/p))^\times$, with $M/p \neq 0$, and assume $j$ lies in the level-one $q$-expansion function field over $\mathbb{Q}$; let $\mathfrak{X}$ be an `XHDRModelAtP` datum for these data. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a non-unit in $A$, with algebraically closed residue field $\kappa$ of characteristic $p$, and $\rho : R_p \to A$ a ring map compatible with $R_p \to \overline{\mathbb{Q}}$. Let $pb \in (\mathbb{Z}/(M/p))^\times$ represent $p$, and let $\delta$ act on places of $\bar F =$ the $q$-expansion function field of $\Gamma_N(p,M,H)$ over $\kappa$ as the semilinear automorphism coming from the mod-$\ell$ diamond operator at level $M/p$ attached to a $\Gamma_0(M/p)$-lift of $pb$. Let $\theta$ be an $\overline{\mathbb{Q}}$-automorphism of $F_M =$ `xHFunctionFieldBar M H` satisfying the $w$-generation property `hwgen` (two $\overline{\mathbb{Q}}$-points of $\mathfrak{X}.\mathrm{Meta}.C$ whose images agree after composing with $\mathfrak{X}.\mathrm{eeta}$, the first projection and $\mathfrak{X}.w$ have places related by $\theta$), and let $\alpha : F_{M/p} \to F_M$ be an $\overline{\mathbb{Q}}$-algebra map which is the identity on underlying Laurent series, with $\alpha$ and $\theta \circ \alpha$ integral. Let $P_{\mathrm{sp}}$ be a `JHPlaceSpecialization` and $R$ a `ProlongationDatum` for $P_{\mathrm{sp}}$ and $\theta$. Assume the norm-reduction hypothesis `hN`: for every $f$ in the integers of both $R_1$ and $R_2$ with both residues nonzero there is a nonzero $g \in \bar F$ such that the $P_{\mathrm{sp}}$-pushforward of the divisor of $\mathrm{Norm}_{F_{M/p}}(f)$ (norm for the algebra structure along $\alpha$) is the divisor of $g$, and $\operatorname{ord}_{\varphi u} g = \operatorname{ord}_{\varphi u} \bar f_1 + \operatorname{ord}_u \bar f_2$ for all places $u$, where $\varphi$ is the mod-$p$ Frobenius operation `qExpFrobeniusPlaceModL` on places. The conclusion is `R.OrderLawFixed` for $\alpha$, $\theta \circ \alpha$ and $\delta$: for every such $f$, every divisor $D$ on places of $F_M$ with $D(W) = \operatorname{ord}_W f$, and every place $v$ of $\bar F$ with $\varphi(\delta(\varphi v)) = v$ which is affine (some $x \in \bar F$ with Laurent series $j$ takes a value in $\kappa$ at $v$), the pushforward of $D$ along $W \mapsto P_{\mathrm{sp}}(W|_\alpha)$ satisfies $(\,(W \mapsto P_{\mathrm{sp}}(W|_\alpha))_* D\,)(v) = \operatorname{ord}_v \bar f_1 + \operatorname{ord}_{\delta(\varphi v)} \bar f_2$.
--
--   This is the order law at the fixed (collision) places in the place-specialization package for $X_H(M)$ at a prime $p$ exactly dividing $M$, the geometric input for computing the reduction of divisors of functions on the two branches of the special fibre. It feeds the construction of a place specialization together with a prolongation datum whose glued specialization controls the component group off the diagonal.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_orderLawFixed_prolongationDatum_of_norm.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_AlgebraicCurve_RatFuncPlaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP
open AlgebraicCurve

open scoped MatrixGroups

set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.XHDRModelAtP.orderLawFixed_prolongationDatum_of_norm
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

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hα : α.IsIntegral) (hβ : (θ.toAlgHom.comp α).IsIntegral)
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)
    (hN : ∀ (f : ↥(xHFunctionFieldBar M H)) (h₁ : f ∈ Rpd.R₁.integers) (h₂ : f ∈ Rpd.R₂.integers),
        Rpd.R₁.residue ⟨f, h₁⟩ ≠ 0 → Rpd.R₂.residue ⟨f, h₂⟩ ≠ 0 →
        letI := algebraAlong α
        ∃ g : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A), g ≠ 0 ∧
          (∀ D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)),
            (∀ V, D V = V.ord (Algebra.norm ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) f)) →
            ∀ v', Finsupp.mapDomain Psp.sp D v' = v'.ord g) ∧
          ∀ u : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)),
            (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p u).ord g =
              (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p u).ord (Rpd.R₁.residue ⟨f, h₁⟩) +
                u.ord (Rpd.R₂.residue ⟨f, h₂⟩)) :
    Rpd.OrderLawFixed α (θ.toAlgHom.comp α) hα hβ δ := by sorry
