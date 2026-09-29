-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_cuspLocalSemicontinuityInfty_prolongationDatum_of_residue
-- name    : ModularCurve.XHDRModelAtP.cuspLocalSemicontinuityInfty_prolongationDatum_of_residue
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/a2fe6f5b-a48e-5afb-a25f-3301e8d788e8
-- title:
--   Local semicontinuity at the ∞-side cusps, first prolongation
-- statement:
--   Fix a prime $p$ and a level $M$ with $p \mid M$ but $p^2 \nmid M$, together with a subgroup $H \le (\mathbb Z/M)^\times$ containing every unit that reduces to $1$ in $(\mathbb Z/(M/p))^\times$, and assume $j$ lies in the level-one $q$-expansion function field over $\mathbb Q$. Let $\mathfrak X$ be a model `XHDRModelAtP p M H hpM hj`, let $A$ be a valuation subring of $\overline{\mathbb Q}$ with $p$ a non-unit of $A$ whose residue field $\kappa$ is algebraically closed of characteristic $p$, and let $\rho : R_p \to A$ lift the structural map $R_p \to \overline{\mathbb Q}$. Let $pb$ be a unit of $\mathbb Z/(M/p)$ represented by $p$, and let $\delta$ be the map on places of $\bar F' =$ `Fbar p M H hpM κ` given by acting with the semilinear automorphism attached to the diamond automorphism `diamondActionModL` at level $M/p$ for `infSubgroup p M H hpM` and the $\Gamma_0$-lift of $pb$. Let $\theta$ be a $\overline{\mathbb Q}$-algebra automorphism of $F_M =$ `xHFunctionFieldBar M H`, pinned by the hypothesis that for $\overline{\mathbb Q}$-points $y, y'$ of $\mathfrak X.\mathrm{Meta}$ whose images in the generic fibre are related by $\mathfrak X.w$, the associated places satisfy $\mathrm{pointEquivPlace}\,y' = \theta \cdot \mathrm{pointEquivPlace}\,y$. Let $\alpha : F_{M/p} \to F_M$ be a $\overline{\mathbb Q}$-algebra map that is the identity on underlying Laurent series, with $\alpha$ and $\theta \circ \alpha$ integral. Let $\mathrm{Psp}$ be a specialisation datum `JHPlaceSpecialization p M H hpM A` with reductions $r_1(W) = \mathrm{sp}(W|_\alpha)$ and $r_2(W) = \delta(\mathrm{sp}(W|_{\theta\alpha}))$, and let $\mathrm{Rpd}$ be a prolongation datum for $\mathrm{Psp}$ and $\theta$, consisting of two regular prolongations $R_1, R_2$ of $A$ to $F_M$ with residues in $\bar F'$ satisfying the compatibilities of `ProlongationDatum`. Two further hypotheses are assumed: on $\alpha$-images the second residue is the $p$-power $q$-expansion Frobenius `qExpFrobeniusModL` of the first residue, and the model is compatible with the reductions in component coordinates, in the sense that for $i \in \{0,1\}$, a point $y$, a lift $u$ over $\operatorname{Spec}\rho$ with $u$ restricting along $A \to \overline{\mathbb Q}$ to $y$, a compatible section $u_\kappa$ of the special fibre, and a closed point $P_0$ of $\mathfrak X.\mathrm{Mfib}$ lying over the point cut out by $u_\kappa$ in the $i$-th component, the place of $P_0$ equals $r_1$ (if $i = 0$) or $r_2$ (otherwise) of the place of $y$. The conclusion is that for every $f \in F_M$ lying in the valuation ring of $R_1$ with $\mathrm{res}_1 f \ne 0$, every divisor $D$ on $F_M$ with $D(W) = \operatorname{ord}_W f$ for all $W$, and every place $v$ of $\bar F'$ over $\kappa$ such that $v = r_1(c)$ for some $\infty$-side place $c$ (that is, $c$ is cuspidal and admits $x, x' \in F_M$ with Laurent expansions $j$ and its $p$-fold $q$-expansion twist, and $\tau \in A$ of residue $1$ with $c(x'/x^p) = \tau$), if $D(W) \ge 0$ for every $\infty$-side $W$ with $r_1(W) = v$, then the pushforward along $r_1$ of the restriction of $D$ to the $\infty$-side places satisfies $(r_{1*}(D|_\infty))(v) \le \operatorname{ord}_v(\mathrm{res}_1 f)$.
--
--   This is the $\infty$-side half of the local semicontinuity of orders at the cusps of $X_H(M)$ at a prime exactly dividing $M$: the sum of the orders of $f$ at the $\infty$-side cusps reducing to a fixed place $v$ of the special fibre is bounded by the order of the first residue of $f$ at $v$. It is stated one-sidedly, using only $R_1$-integrality of $f$, which allows the $0$-side companion [`ModularCurve.XHDRModelAtP.cuspLocalSemicontinuityZero_prolongationDatum_of_residue`](thm.html#ModularCurve.XHDRModelAtP.cuspLocalSemicontinuityZero_prolongationDatum_of_residue) to be obtained by transport along $\theta$; both are combined in [`ModularCurve.XHDRModelAtP.cuspLocalSemicontinuity_prolongationDatum_of_residue`](thm.html#ModularCurve.XHDRModelAtP.cuspLocalSemicontinuity_prolongationDatum_of_residue).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_cuspLocalSemicontinuityInfty_prolongationDatum_of_residue.lean

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
open Classical in

theorem ModularCurve.XHDRModelAtP.cuspLocalSemicontinuityInfty_prolongationDatum_of_residue
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
      Rpd.R₂.residue ⟨α v, h₂⟩ = qExpFrobeniusModL (ResidueField ↥A) (ΓN p M H hpM) p (Rpd.R₁.residue ⟨α v, h₁⟩))

    (hcomp : (∀ (i : Fin 2)
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
        else Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ (𝔛.Meta.pointEquivPlace y))) :
    ∀ (f : ↥(xHFunctionFieldBar M H)) (h₁ : f ∈ Rpd.R₁.integers),
      Rpd.R₁.residue ⟨f, h₁⟩ ≠ 0 →
        ∀ D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), (∀ W, D W = W.ord f) →
          ∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)),
            (∃ c, (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A)) c ∧ (Psp.reduceFst α hα) c = v) →
            (∀ W, (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A)) W → (Psp.reduceFst α hα) W = v → 0 ≤ D W) →
            Finsupp.mapDomain (Psp.reduceFst α hα) (D.filter (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A))) v ≤ v.ord (Rpd.R₁.residue ⟨f, h₁⟩) := by sorry
