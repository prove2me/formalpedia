-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_cuspLocalSemicontinuityZero_prolongationDatum_of_residue
-- name    : ModularCurve.XHDRModelAtP.cuspLocalSemicontinuityZero_prolongationDatum_of_residue
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/3f9f5715-7353-5f65-b2d7-7776238b47b9
-- title:
--   Semicontinuity of 0-side cusp orders under the second reduction
-- statement:
--   Fix a prime $p$ and $M \neq 0$ with $p \mid M$ but $p^2 \nmid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit that reduces to $1$ in $(\mathbb{Z}/(M/p))^\times$, and $M/p \neq 0$; assume $j(q)$ lies in the $q$-expansion function field of $\mathrm{SL}_2(\mathbb{Z})$, and let $\mathfrak{X}$ be an integral model datum `XHDRModelAtP` for $X_H(M)$ over $R(p)$, with its curve model $\mathfrak{X}.\mathrm{Meta}$ over $\overline{\mathbb{Q}}$ having function field $F_M =$ `xHFunctionFieldBar M H`. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $A$, whose residue field $\kappa$ is algebraically closed of characteristic $p$, and $\rho : R(p) \to A$ a ring map inducing the structure map to $\overline{\mathbb{Q}}$. Let $pb$ be a unit of $\mathbb{Z}/(M/p)$ represented by $p$, and let $\delta$ act on places of $\bar F' =$ `Fbar p M H hpM κ` as the semilinear automorphism attached to the mod-$\ell$ diamond automorphism `diamondActionModL` at the $\Gamma_0(M/p)$-lift of $pb$. Let $\theta$ be a $\overline{\mathbb{Q}}$-algebra automorphism of $F_M$ pinned by the requirement that whenever two $\overline{\mathbb{Q}}$-sections $y, y'$ of $\mathfrak{X}.\mathrm{Meta}$ satisfy $y'$ followed by `eeta`, the first pullback projection and $\mathfrak{X}.w$ equals $y$ followed by `eeta` and the first projection, the associated places satisfy $\mathrm{place}(y') = \theta \cdot \mathrm{place}(y)$. Let $\alpha : F_{M/p} \to F_M$ be a $\overline{\mathbb{Q}}$-algebra map, where $F_{M/p} =$ `xHFunctionFieldBar (M/p) (infSubgroup p M H hpM)`, which is the identity on underlying Laurent series, with $\alpha$ and $\theta \circ \alpha$ integral. Let $Psp$ be a place-specialisation datum `JHPlaceSpecialization` with specialisation map $\mathrm{sp}$, and $Rpd$ a prolongation datum for $Psp$ and $\theta$, consisting of two regular prolongations $R_1, R_2$ of $A$ to $F_M$ with values in $\bar F'$ such that $R_2$-integrality and $R_2$-residues are computed from $R_1$ through $\theta$. Assume: on $\alpha$-images that are integral for both, the $R_2$-residue is `qExpFrobeniusModL` applied to the $R_1$-residue; and a compatibility $hcomp$ saying that for each $i \in \{0,1\}$, each $\overline{\mathbb{Q}}$-section $y$, each lift $u$ of $\rho$ with $\overline{\mathbb{Q}}$-point condition $barPt\,A \circ u = y$ followed by `eeta` and the first projection, each compatible $\kappa$-section $u_\kappa$ of the fibre, and each closed point $P_0$ of the fibre model lying over the closed point of $u_\kappa$, the place of $P_0$ equals $Psp.\mathrm{reduceFst}\,\alpha$ applied to the place of $y$ when $i = 0$, and $Psp.\mathrm{reduceSnd}\,(\theta \circ \alpha)\,\delta$ applied to it otherwise. The conclusion: for every $f \in F_M$ integral for $R_2$ with non-zero $R_2$-residue, every divisor $D$ on $F_M$ with $D(W) = \mathrm{ord}_W(f)$ for all places $W$, and every place $u$ of $\bar F'$ over $\kappa$ which is the $\mathrm{reduceSnd}$-image of some place satisfying `IsZeroSide` (namely: cuspidal in the sense of `IsCuspidal'`, and there are $x, x' \in F_M$ with Laurent expansions $j(q)$ and $j(q^p)$ and some $\tau \in A$ of residue $1$ with $W$ taking the value $\tau$ at $x/x'^p$), if $D(W) \ge 0$ for all `IsZeroSide` places $W$ with $\mathrm{reduceSnd}(W) = u$, then the sum of $D(W)$ over the `IsZeroSide` places $W$ with $\mathrm{reduceSnd}(W) = u$, i.e. the value at $u$ of the pushforward along $\mathrm{reduceSnd}$ of $D$ restricted to the `IsZeroSide` places, is at most $\mathrm{ord}_u$ of the $R_2$-residue of $f$.
--
--   This is the $0$-side half of the local semicontinuity statement for orders at cusps in the integral model of $X_H(M)$ at a prime exactly dividing the level, transported from the $\infty$-side by the Atkin–Lehner automorphism $\theta$ at the level of places. It is combined with its $\infty$-side counterpart in [`ModularCurve.XHDRModelAtP.cuspLocalSemicontinuity_prolongationDatum_of_residue`](thm.html#ModularCurve.XHDRModelAtP.cuspLocalSemicontinuity_prolongationDatum_of_residue).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_cuspLocalSemicontinuityZero_prolongationDatum_of_residue.lean

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

theorem ModularCurve.XHDRModelAtP.cuspLocalSemicontinuityZero_prolongationDatum_of_residue
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
    ∀ (f : ↥(xHFunctionFieldBar M H)) (h₂ : f ∈ Rpd.R₂.integers),
      Rpd.R₂.residue ⟨f, h₂⟩ ≠ 0 →
        ∀ D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), (∀ W, D W = W.ord f) →
          ∀ u : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)),
            (∃ c, (JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A)) c ∧ (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ) c = u) →
            (∀ W, (JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A)) W → (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ) W = u → 0 ≤ D W) →
            Finsupp.mapDomain (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ) (D.filter (JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A))) u ≤ u.ord (Rpd.R₂.residue ⟨f, h₂⟩) := by sorry
