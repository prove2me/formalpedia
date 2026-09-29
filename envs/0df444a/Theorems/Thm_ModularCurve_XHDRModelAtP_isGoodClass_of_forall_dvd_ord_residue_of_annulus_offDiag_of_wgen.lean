-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_isGoodClass_of_forall_dvd_ord_residue_of_annulus_offDiag_of_wgen
-- name    : ModularCurve.XHDRModelAtP.isGoodClass_of_forall_dvd_ord_residue_of_annulus_offDiag_of_wgen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/fc00824f-0ea1-57b1-8462-ed4d60ac44e4
-- title:
--   Divisible supersingular root orders give a good class
-- statement:
--   Fix a prime $p$ and a positive integer $M$ with $p \mid M$ (`hpM`) and $p^2 \nmid M$ (`hpM2`), and a subgroup $H \le (\mathbb{Z}/M)^{\times}$ containing every unit whose image under the reduction map $(\mathbb{Z}/M)^{\times} \to (\mathbb{Z}/(M/p))^{\times}$ is trivial (`hHp`). Assume `hj`, that the $q$-series `jqModC ℚ` lies in the function field `qExpFunctionFieldC ℚ ⊤` of level one, and fix a structure $\mathfrak{X} :$ `XHDRModelAtP p M H hpM hj`, that is, an integral model of $X_H(M)$ over `R p` together with the curve model `𝔛.Meta` of $F_M :=$ `xHFunctionFieldBar M H` over $\overline{\mathbb{Q}}$, the isomorphism `𝔛.eeta` onto the generic geometric fibre, and the remaining data and axioms of that structure.
--
--   Let $A$ be a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` lying over $p$ in the sense of `hA`, i.e. $p$ is a non-unit of $A$, with residue field $\kappa :=$ `ResidueField ↥A` of characteristic $p$ and algebraically closed, and let $\rho :$ `R p` $\to A$ be a ring homomorphism whose composite with the inclusion $A \hookrightarrow \overline{\mathbb{Q}}$ is the structure map `algebraMap (R p) (AlgebraicClosure ℚ)` (`hρ`). Write $\bar F :=$ `JHNeronObjectAtP.Fbar p M H hpM κ`, the function field `qExpFunctionFieldC κ (ΓN p M H hpM)` in characteristic $p$.
--
--   The operator $\delta$ on places of $\bar F$ is prescribed by `hδ`: for a unit `pb` of $\mathbb{Z}/(M/p)$ represented by $p$ (`hpb`), $\delta$ is the action on places, through `SemilinearAut.ofAlgAut`, of the automorphism `diamondActionModL κ (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)`, where `infSubgroup p M H hpM` is the image of $H$ in $(\mathbb{Z}/(M/p))^{\times}$ and [`CuspForm.gammaLift`](def/CuspForm_HeckeOperatorFormsGammaH.html#L36) chooses a lift of `pb` to $\Gamma_0(M/p)$; thus $\delta$ is the diamond operator at $p$ in characteristic $p$. The finite set $SS$ of pairs of places of $\bar F$ is prescribed by `hSS` to consist exactly of the elements of `ssNodePairsQExp κ (ΓN p M H hpM) p`, i.e. of those pairs $s$ whose second entry is a supersingular place and whose first entry is the image of the second under `qExpFrobeniusPlaceModL`.
--
--   Further data: an $\overline{\mathbb{Q}}$-algebra automorphism $\theta$ of $F_M$; an $\overline{\mathbb{Q}}$-algebra map $\alpha$ from $F_{M/p} :=$ `xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)` to $F_M$, integral (`hα`), with $\beta := \theta \circ \alpha$ also integral (`hβ`); a place-specialisation structure `Psp : JHPlaceSpecialization p M H hpM A`, whose component `sp` sends places of $F_{M/p}$ to places of $\bar F$ and which carries the divisor, surjectivity, inertia and Frobenius axioms of that structure; and a prolongation datum `Rpd` for `Psp` and $\theta$, consisting of two regular prolongations $R_1, R_2$ of $A$ in $F_M$ with values in $\bar F$, linked by $f \in R_2$ iff $\theta f \in R_1$ and by the equality of the corresponding residues. Throughout, `Psp.reduceFst α hα W` $=$ `Psp.sp` of the restriction of $W$ along $\alpha$, and `Psp.reduceSnd β hβ δ W` $= \delta($ `Psp.sp` of the restriction of $W$ along $\beta)$.
--
--   The comparison hypotheses are as follows. `hwgen` pins $\theta$ to the involution `𝔛.w` of the model: for any two $\overline{\mathbb{Q}}$-points $y, y'$ of `𝔛.Meta.C` over the base, if $y'$ followed by `𝔛.eeta`, the first pullback projection and `𝔛.w.hom` equals $y$ followed by `𝔛.eeta` and the first projection, then `𝔛.Meta.pointEquivPlace y'` is the image of `𝔛.Meta.pointEquivPlace y` under the action of `SemilinearAut.ofAlgAut θ`. `hα_coe` says that $\alpha$ preserves Laurent expansions, and `hβ_coe` that the Laurent expansion of $\beta u$ is `qExpand (AlgebraicClosure ℚ) p` applied to that of $u$, i.e. $q \mapsto q^p$. `hθgal` says that $\theta$ commutes with the action of every $\sigma \in \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ through `arithmeticGalois` on $F_M$.
--
--   The structural laws are: `hTD`, the type dichotomy, for every place $W$ of $F_M$ either `reduceFst W` is the Frobenius image of `reduceSnd W` or $\delta$ applied to the Frobenius image of `reduceFst W` is `reduceSnd W`; `hmodel`, that `Rpd` is a model for $(\alpha, \beta, \delta)$, i.e. the two divisor laws together with the two cusp laws hold; `hO`, the order law at $\delta$-fixed affine places; `hRL`, the regularity law relative to $SS$; and `hNV`, the node-value law relative to $SS$ (these four are the conjunctions recorded in `IsModel`, `OrderLawFixed`, `RegularityLaw` and `NodeValueLaw`).
--
--   Two compatibilities relate the two readings to reduction of sections. For $i \in \{0,1\}$, an $\overline{\mathbb{Q}}$-point $y$ of `𝔛.Meta.C` over the base, a section $u$ of `toBase p (ΓM M H) hj` over `Spec.map ρ` whose $\overline{\mathbb{Q}}$-specialisation `barPt A ≫ u.1` agrees with the generic reading of $y$, a $\kappa$-point $u_\kappa$ of the fibre over `(residue ↥A) ∘ ρ` reducing $u$ and splitting the base, and a closed point $P_0$ of the fibre curve model `(𝔛.Mfib A hA ρ hρ).C` whose image under `𝔛.efib` followed by `𝔛.comp … i` is the image of the closed point under $u_\kappa$: `hcompat` asserts that `(𝔛.Mfib A hA ρ hρ).placeOfPoint P0` equals `Psp.reduceFst α hα (𝔛.Meta.pointEquivPlace y)` when $i = 0$ and `Psp.reduceSnd β hβ δ (𝔛.Meta.pointEquivPlace y)` otherwise; `hcompat'` asserts, under the same hypotheses, that for $i = 0$ the place `Psp.reduceSnd β hβ δ (𝔛.Meta.pointEquivPlace y)` is $\delta$ of the `qExpFrobeniusPlaceModL`-image of `placeOfPoint P0`, and for $i \neq 0$ that `Psp.reduceFst α hα (𝔛.Meta.pointEquivPlace y)` is the `qExpFrobeniusPlaceModL`-image of `placeOfPoint P0`.
--
--   The node annuli are given by `e`, `he` and `hAnn`: a function $e$ on $SS$ with $e(s) > 0$, and for each $s \in SS$ an annulus `An : AlgebraicCurve.Annulus A F_M` (a set `An.dom` of places, a parameter `An.param`, a modulus `An.modulus` in the maximal ideal of $A$, subject to the axioms of that structure) such that: a place $W$ of $F_M$ lies in `An.dom` precisely when `Psp.reduceFst α hα W` $= s_1$ and $W$ is neither strict of the first kind nor strict of the second kind, where strictness of the first kind means $\delta$ of the Frobenius image of `reduceFst W` equals `reduceSnd W` with `reduceFst W` not $\delta$-fixed, and strictness of the second kind means `reduceFst W` is the Frobenius image of `reduceSnd W` with `reduceSnd W` not $\delta$-fixed; the modulus is $p^{e(s)}$ times a unit of $A$; the parameter is fixed by the `arithmeticGalois` action of every $\sigma$ in the inertia subgroup of $A$ over $\mathbb{Q}$; the product of the image of `An.modulus`$^{-1}$ with `An.param` lies in the integers of $R_1$; `An.param` lies in the integers of $R_2$ with non-zero residue; `An.param` has $R_2$-residue of order $1$ at $s_2$, and for every $f$ in the integers of $R_2$ with non-zero residue and $\operatorname{ord}_P f = 0$ for all $P \in$ `An.dom`, at each such $P$ the element $f(P) \cdot (\mathrm{param}(P))^{-\operatorname{ord}_{s_2}(\text{res}_2 f)}$ lies in $A$ and is a unit there; and symmetrically, `An.modulus` $\cdot$ `An.param`$^{-1}$ lies in the integers of $R_1$, has $R_1$-residue of order $1$ at $s_1$, and for every $f$ in the integers of $R_1$ with non-zero residue and vanishing order along `An.dom`, at each $P \in$ `An.dom` the element $f(P) \cdot \big((\mathrm{modulus} \cdot \mathrm{param}^{-1})(P)\big)^{-\operatorname{ord}_{s_1}(\text{res}_1 f)}$ lies in $A$ and is a unit; here $\operatorname{ord}$ is the normalised order of a place and evaluation is `Place.evalAt`.
--
--   Finally let $n > 0$, let $x \in J_H(M) =$ `Pic0` of $F_M$ over $\overline{\mathbb{Q}}$, let $D$ be a degree-zero divisor with `Pic0.mk D = x` (`hDx`), and let $f \in F_M$ satisfy $n \cdot D(W) = \operatorname{ord}_W f$ for every place $W$ (`hf`), so that $f$ is an $n$-th root function for $D$. Assume $f$ lies in the integers of $R_1$ (`h₁`) with non-zero residue (`hr₁`), and assume `hroot`: for every $s \in SS$, the integer $n$ divides $\operatorname{ord}_{s_1}$ of the $R_1$-residue of $f$, the order being taken at the first entry of the node pair.
--
--   The conclusion is `Psp.IsGoodClass α (θ.toAlgHom.comp α) hα hβ δ SS x`: there exists a degree-zero divisor $D'$ of $F_M$ over $\overline{\mathbb{Q}}$ such that the predicate `Psp.IsGoodDiv α β hα hβ δ` holds for $D'$, the associated gluing datum `Psp.glueData α β hα hβ δ SS D'` lies in `GluingData.admissible SS`, and `Pic0.mk D' = x`. The witnessing divisor is not required to be the given $D$.
--
--   This is the criterion, in root-function form, that a class in $J_H(M)(\overline{\mathbb{Q}})$ whose reduced $n$-th root function has orders divisible by $n$ at the supersingular node places is represented by a divisor that is good and admissibly glued across the two components of the geometric special fibre of the Deligne–Rapoport model at a prime $p$ exactly dividing $M$ — Raynaud's description of the identity component of the Néron model of $J_H(M)$, transcribed into the language of places, annuli and prolongations. It feeds the statement that the points of $J_H(M)$ extend to places of the Néron object at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_isGoodClass_of_forall_dvd_ord_residue_of_annulus_offDiag_of_wgen.lean

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

theorem ModularCurve.XHDRModelAtP.isGoodClass_of_forall_dvd_ord_residue_of_annulus_offDiag_of_wgen
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

    (e : ↥SS → ℕ) (he : ∀ s, 0 < e s)
    (hAnn : ∀ s : ↥SS, ∃ An : AlgebraicCurve.Annulus A ↥(xHFunctionFieldBar M H),
      (∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
        W ∈ An.dom ↔ (Psp.reduceFst α hα W = s.1.1 ∧ ¬ Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W ∧ ¬ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ W)) ∧
      (∃ u : ↥A, IsUnit u ∧ An.modulus = ((p : ℕ) : ↥A) ^ (e s) * u) ∧
      (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.inertiaSubgroupIn ℚ →
        (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • An.param = An.param) ∧
      algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((An.modulus : AlgebraicClosure ℚ))⁻¹ * An.param ∈ Rpd.R₁.integers ∧
      (∃ h₂ : An.param ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨An.param, h₂⟩ ≠ 0) ∧

      (∃ h₂ : An.param ∈ Rpd.R₂.integers, s.1.2.ord (Rpd.R₂.residue ⟨An.param, h₂⟩) = 1 ∧
        ∀ (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨f, hf⟩ ≠ 0 →
          (∀ P ∈ An.dom, P.ord f = 0) → ∀ P ∈ An.dom,
            ∃ h : P.evalAt f * (P.evalAt An.param) ^ (-(s.1.2.ord (Rpd.R₂.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A)) ∧
      (∃ h₁ : algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((An.modulus : ↥A) : AlgebraicClosure ℚ) * An.param⁻¹ ∈ Rpd.R₁.integers,
        s.1.1.ord (Rpd.R₁.residue ⟨_, h₁⟩) = 1 ∧
        ∀ (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨f, hf⟩ ≠ 0 →
          (∀ P ∈ An.dom, P.ord f = 0) → ∀ P ∈ An.dom,
            ∃ h : P.evalAt f * (P.evalAt (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((An.modulus : ↥A) : AlgebraicClosure ℚ) * An.param⁻¹)) ^
              (-(s.1.1.ord (Rpd.R₁.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A)))

    (n : ℕ) (hn : 0 < n) (x : JH M H)
    (D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H))))
    (hDx : Pic0.mk D = x)
    (f : ↥(xHFunctionFieldBar M H))
    (hf : ∀ W, (n : ℤ) * (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) W = W.ord f)
    (h₁ : f ∈ Rpd.R₁.integers) (hr₁ : Rpd.R₁.residue ⟨f, h₁⟩ ≠ 0)

    (hroot : ∀ s ∈ SS, (n : ℤ) ∣ s.1.ord (Rpd.R₁.residue ⟨f, h₁⟩)) :
    Psp.IsGoodClass α (θ.toAlgHom.comp α) hα hβ δ SS x := by sorry
