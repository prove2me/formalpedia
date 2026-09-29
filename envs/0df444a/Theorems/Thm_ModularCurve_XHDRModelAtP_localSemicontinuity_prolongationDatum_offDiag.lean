-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_localSemicontinuity_prolongationDatum_offDiag
-- name    : ModularCurve.XHDRModelAtP.localSemicontinuity_prolongationDatum_offDiag
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/263463d1-7678-5c59-b711-67bea3c150b7
-- title:
--   Off-diagonal semicontinuity for the prolongation datum at p ‖ M
-- statement:
--   Fix a prime $p$ and $M$ with $p \mid M$ but $p^2 \nmid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit that reduces to $1$ in $(\mathbb{Z}/(M/p))^\times$, and the hypothesis $hj$ that $j$, as a $q$-expansion, lies in the level-$\mathrm{SL}(2,\mathbb{Z})$ function field over $\mathbb{Q}$. Let $\mathfrak{X}$ be an `XHDRModelAtP` package for $(p,M,H)$, let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $A$, residue field $\kappa$ algebraically closed of characteristic $p$, and let $\rho : R_p \to A$ be compatible with $R_p \to \overline{\mathbb{Q}}$. Let $pb$ be a unit of $\mathbb{Z}/(M/p)$ represented by $p$, and let $\delta$ be the map on places of $\bar F =$ `Fbar` $p\,M\,H$ given by the semilinear action of the diamond automorphism $\langle pb \rangle$ at level $\Gamma_H(M/p)$. Let $\theta$ be a $\overline{\mathbb{Q}}$-algebra automorphism of $F =$ `xHFunctionFieldBar` $M\,H$ satisfying the compatibility `hwgen` with the morphism $\mathfrak{X}.w$ on $\overline{\mathbb{Q}}$-points of the curve model $\mathfrak{X}.\mathrm{Meta}$, and let $\alpha$ be a $\overline{\mathbb{Q}}$-algebra map from `xHFunctionFieldBar` $(M/p)$ `(infSubgroup p M H hpM)` into $F$ which is the identity on Laurent-series representatives, with $\alpha$ and $\theta \circ \alpha$ integral. Let $Psp$ be a `JHPlaceSpecialization` for $(p,M,H,A)$ and $Rpd$ a `ProlongationDatum` for $Psp$ and $\theta$, consisting of two regular prolongations $R_1, R_2$ of $A$ to $F$ with values in $\bar F$, the second being the first precomposed with $\theta$. Two further hypotheses are assumed, for $i \in \{0,1\}$, each $\overline{\mathbb{Q}}$-point $y$ of $\mathfrak{X}.\mathrm{Meta}$, each lift $u$ of $y$ over $\operatorname{Spec} A$, each compatible $\kappa$-point $u\kappa$ of the fibre, and each closed point $P_0$ of the fibre curve model $\mathfrak{X}.\mathrm{Mfib}$ mapping under $\mathfrak{X}.\mathrm{efib}$ followed by the $i$-th component map to the closed point of $u\kappa$: the diagonal clause `hcomp`, that the place of $P_0$ is $Psp.\mathrm{reduceFst}$ of the place of $y$ when $i = 0$ and $Psp.\mathrm{reduceSnd}$ (with $\theta \circ \alpha$ and $\delta$) of that place otherwise; and the off-diagonal clause `hcompat'`, that for $i = 0$ the second reading of the place of $y$ equals $\delta$ applied to the mod-$p$ Frobenius pullback `qExpFrobeniusPlaceModL` of the place of $P_0$, while for $i = 1$ the first reading equals that Frobenius pullback. The conclusion is the conjunction of two symmetric assertions. For the first: for every $f \in F$ lying in the integers of both $R_1$ and $R_2$ with both residues non-zero, every divisor $D$ on $F$ with $D(W) = \operatorname{ord}_W f$ at every place $W$, and every place $v$ of $\bar F$ with $\Phi(\delta(\Phi v)) \ne v$ (where $\Phi$ is the Frobenius pullback), if $D(W) \ge 0$ at every place $W$ that is strict of the first kind (that is, $\delta(\Phi(\mathrm{reduceFst}\,W)) = \mathrm{reduceSnd}\,W$ and $\mathrm{reduceFst}\,W$ is not $\delta$-fixed in the above sense) with $\mathrm{reduceFst}\,W = v$, then the push-forward along $\mathrm{reduceFst}$ of the part of $D$ supported on strict first-kind places, evaluated at $v$, is at most $\operatorname{ord}_v$ of the $R_1$-residue of $f$. The second assertion is the same with $\mathrm{reduceSnd}$ (formed from $\theta \circ \alpha$ and $\delta$), the strict second-kind part of $D$, and the $R_2$-residue of $f$.
--
--   This is the local upper semicontinuity of the order of vanishing under specialisation on the Deligne–Rapoport model, read in the two components of the fibre at $p$: each residue of a common unit of the two prolongations dominates the push-forward of the corresponding strict part of its divisor, away from the places where the Frobenius–diamond correspondence collides. It supplies the two divisor laws needed to assemble the glued specialisation with its component-group data in [`ModularCurve.XHDRModelAtP.exists_jHPlaceSpecialization_prolongationDatum_gluedSpecialization_componentGroup_offDiag_of_wgen`](thm.html#ModularCurve.XHDRModelAtP.exists_jHPlaceSpecialization_prolongationDatum_gluedSpecialization_componentGroup_offDiag_of_wgen).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_localSemicontinuity_prolongationDatum_offDiag.lean

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

theorem ModularCurve.XHDRModelAtP.localSemicontinuity_prolongationDatum_offDiag
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
        else Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ (𝔛.Meta.pointEquivPlace y)))

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
            qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint P0)) :
    ((∀ (f : ↥(xHFunctionFieldBar M H)) (h₁ : f ∈ Rpd.R₁.integers) (h₂ : f ∈ Rpd.R₂.integers),
      Rpd.R₁.residue ⟨f, h₁⟩ ≠ 0 → Rpd.R₂.residue ⟨f, h₂⟩ ≠ 0 →
      ∀ D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), (∀ W, D W = W.ord f) →
        ∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), ¬ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v →
          (∀ W, Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W → Psp.reduceFst α hα W = v → 0 ≤ D W) →
          Finsupp.mapDomain (Psp.reduceFst α hα) (Psp.fstDiv α (θ.toAlgHom.comp α) hα hβ δ D) v ≤ v.ord (Rpd.R₁.residue ⟨f, h₁⟩)) ∧
     (∀ (f : ↥(xHFunctionFieldBar M H)) (h₁ : f ∈ Rpd.R₁.integers) (h₂ : f ∈ Rpd.R₂.integers),
      Rpd.R₁.residue ⟨f, h₁⟩ ≠ 0 → Rpd.R₂.residue ⟨f, h₂⟩ ≠ 0 →
      ∀ D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), (∀ W, D W = W.ord f) →
        ∀ u : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), ¬ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ u →
          (∀ W, Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ W → Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ W = u → 0 ≤ D W) →
          Finsupp.mapDomain (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ) (Psp.sndDiv α (θ.toAlgHom.comp α) hα hβ δ D) u ≤
            u.ord (Rpd.R₂.residue ⟨f, h₂⟩))) := by sorry
