-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_exists_mapDomain_sp_eq_ord_and_ord_frob_eq_add_of_norm_of_prolongationDatum
-- name    : ModularCurve.XHDRModelAtP.exists_mapDomain_sp_eq_ord_and_ord_frob_eq_add_of_norm_of_prolongationDatum
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/84972f1f-1e4a-511e-8175-0735edb71e53
-- title:
--   Reduction of the norm along α of a doubly integral function
-- statement:
--   Fix a prime $p$ and $M \ne 0$ with $p \mid M$ and $p^2 \nmid M$, a subgroup $H \le (\mathbb Z/M)^\times$ containing every unit that reduces to $1$ modulo $M/p$, and assume $M/p \ne 0$; let $\mathrm{jqModC}\,\mathbb Q$ lie in the $q$-expansion function field of $\mathrm{SL}(2,\mathbb Z)$ and let $\mathfrak X$ be a model datum `XHDRModelAtP p M H hpM hj`. Let $A$ be a valuation subring of $\overline{\mathbb Q}$ with $p$ in its non-units, whose residue field $\kappa$ has characteristic $p$ and is algebraically closed, and let $\rho : R_p \to A$ be a ring homomorphism whose composite with the inclusion of $A$ is the structure map $R_p \to \overline{\mathbb Q}$. Let $pb$ be a unit of $\mathbb Z/(M/p)$ represented by $p$, and let $\delta$ be the self-map of the set of places of $\bar F' := \mathrm{Fbar}\,p\,M\,H$ over $\kappa$ given by the action of the semilinear automorphism attached to the diamond automorphism `diamondActionModL` at the $\Gamma_0(M/p)$-lift of $pb$. Let $\theta$ be an $\overline{\mathbb Q}$-algebra automorphism of $F_M := \overline{\mathbb Q}\cdot F(\Gamma_H(M))$ such that any two $\overline{\mathbb Q}$-points of $\mathfrak X.\mathrm{Meta}$ related by $\mathfrak X.w$ after $\mathfrak X.\mathrm{eeta}$ followed by the first projection have their associated places exchanged by $\theta$; let $\alpha : F_{M/p} \to F_M$ be an $\overline{\mathbb Q}$-algebra map which is the identity on underlying Laurent series, with both $\alpha$ and $\theta \circ \alpha$ integral. Let $P_{\mathrm{sp}}$ be a `JHPlaceSpecialization` for $(p,M,H,A)$, with place map $\mathrm{sp}$ from places of $F_{M/p}$ to places of $\bar F'$, and $R$ a `ProlongationDatum` for $P_{\mathrm{sp}}$ and $\theta$, consisting of two regular prolongations $R_1, R_2$ of $A$ to $F_M$ with residues in $\bar F'$, related by $f \in R_2.\mathrm{integers} \iff \theta f \in R_1.\mathrm{integers}$ and $R_2.\mathrm{residue}\,f = R_1.\mathrm{residue}\,(\theta f)$; assume that for every $v \in F_{M/p}$ with $\alpha v$ integral for both, the $R_2$-residue of $\alpha v$ is the image of its $R_1$-residue under the $p$-power $q$-expansion Frobenius `qExpFrobeniusModL`. Then for every $f \in F_M$ integral for $R_1$ and $R_2$ with both residues non-zero, regarding $F_M$ as an $F_{M/p}$-algebra via $\alpha$, there is a non-zero $g \in \bar F'$ such that, first, for every divisor $D$ on $F_{M/p}$ whose coefficient at each place $V$ is $V.\mathrm{ord}$ of the norm $N_{F_M/F_{M/p}}(f)$, the pushforward $\mathrm{sp}_* D$ has coefficient $v'.\mathrm{ord}\,g$ at every place $v'$ of $\bar F'$, and second, for every place $u$ of $\bar F'$, the order of $g$ at the Frobenius-pullback place $\varphi u$ equals the order of $R_1.\mathrm{residue}\,f$ at $\varphi u$ plus the order of $R_2.\mathrm{residue}\,f$ at $u$.
--
--   This is the reduction-of-the-norm, or Gauss-norm compatibility, step for the two prolongations of a place of $\overline{\mathbb Q}$ above $p$ to the function field of $X_H(M)$ with $p \parallel M$: the norm of $f$ along the degeneracy embedding $\alpha$ has reduction $\bar f_1 \cdot \varphi^* \bar f_2$, which is recorded here both as a divisor identity after specialisation and as an order formula at Frobenius-pullback places. It feeds the divisor and order laws used in the construction of the glued specialisation and of the component-group data attached to $\mathfrak X$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_exists_mapDomain_sp_eq_ord_and_ord_frob_eq_add_of_norm_of_prolongationDatum.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_AlgebraicCurve_RatFuncPlaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve
  IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP
open scoped MatrixGroups

set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.XHDRModelAtP.exists_mapDomain_sp_eq_ord_and_ord_frob_eq_add_of_norm_of_prolongationDatum
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

    (hres₂α : ∀ (v : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) (h₁ : α v ∈ Rpd.R₁.integers) (h₂ : α v ∈ Rpd.R₂.integers),
      Rpd.R₂.residue ⟨α v, h₂⟩ = qExpFrobeniusModL (ResidueField ↥A) (ΓN p M H hpM) p (Rpd.R₁.residue ⟨α v, h₁⟩)) :
    ∀ (f : ↥(xHFunctionFieldBar M H)) (h₁ : f ∈ Rpd.R₁.integers) (h₂ : f ∈ Rpd.R₂.integers),
        Rpd.R₁.residue ⟨f, h₁⟩ ≠ 0 → Rpd.R₂.residue ⟨f, h₂⟩ ≠ 0 →
        letI := algebraAlong α
        ∃ g : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A), g ≠ 0 ∧
          (∀ D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)),
            (∀ V, D V = V.ord (Algebra.norm ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) f)) →
            ∀ v', Finsupp.mapDomain Psp.sp D v' = v'.ord g) ∧
          ∀ u : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)),
            (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p u).ord g =
              (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p u).ord (Rpd.R₁.residue ⟨f, h₁⟩) +
                u.ord (Rpd.R₂.residue ⟨f, h₂⟩) := by sorry
