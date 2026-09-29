-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_exists_ord_residue_eq_and_ord_eq_of_nonneg_of_isUnit_mul_modulus_zpow_eq_prod_neg_evalAt_zpow_of_annulus_offDiag_of_wgen
-- name    : ModularCurve.XHDRModelAtP.exists_ord_residue_eq_and_ord_eq_of_nonneg_of_isUnit_mul_modulus_zpow_eq_prod_neg_evalAt_zpow_of_annulus_offDiag_of_wgen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/74a63fd9-bf37-57bc-89b1-71bf3aee4eba
-- title:
--   Placement of an effective configuration on a node annulus
-- statement:
--   Fix a prime $p$ and a natural number $M$ with $p \mid M$ (`hpM`) and $p^2 \nmid M$ (`hpM2`), a subgroup $H \le (\mathbb{Z}/M)^{\times}$ which contains every unit whose image under the reduction map `ZMod.unitsMap` to $(\mathbb{Z}/(M/p))^{\times}$ is $1$ (`hHp`), and the hypothesis `hj` that the $q$-series `jqModC ℚ` lies in the field `qExpFunctionFieldC ℚ ⊤`. Let $\mathfrak{X}$ be a model datum `XHDRModelAtP p M H hpM hj`, so in particular it carries a curve model $\mathfrak{X}.\mathrm{Meta}$ over $\overline{\mathbb{Q}}$ with function field $F_M :=$ `xHFunctionFieldBar M H` (the base change to $\overline{\mathbb{Q}}$ of the $q$-expansion field of $X_H(M)$ inside Laurent series), an isomorphism $\mathfrak{X}.\mathrm{eeta}$ onto the generic geometric fibre of `toBase p (ΓM M H) hj`, and the further structure of that record.
--
--   The arithmetic base consists of a valuation subring $A \subseteq \overline{\mathbb{Q}}$ with $p$ a non-unit of $A$ (`hA`, i.e. `A.LiesOverPrime p`), whose residue field $\kappa$ is algebraically closed of characteristic $p$, together with a ring homomorphism $\rho : R_p \to A$ lifting the structure map, in the sense that $A$'s inclusion composed with $\rho$ is `algebraMap (R p) (AlgebraicClosure ℚ)` (`hρ`). Write $F_{M/p} :=$ `xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)`, where `infSubgroup` is the image of $H$ in $(\mathbb{Z}/(M/p))^{\times}$, and $\bar F :=$ `JHNeronObjectAtP.Fbar p M H hpM κ`, the $q$-expansion function field over $\kappa$ at level `ΓN p M H hpM`.
--
--   A unit $pb$ of $\mathbb{Z}/(M/p)$ representing the class of $p$ (`hpb`) is fixed, and $\delta$ is a self-map of the places of $\bar F$ over $\kappa$ which, by `hδ`, acts as the semilinear automorphism attached to the diamond automorphism `diamondActionModL κ (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)`. The finite set $SS$ of pairs of places is characterised by `hSS` as consisting exactly of the pairs $s$ with $s_2$ a supersingular place (`ssPlacesQExp κ (ΓN p M H hpM) p`) and $s_1 =$ `qExpFrobeniusPlaceModL κ (ΓN p M H hpM) p` applied to $s_2$, i.e. the node pairs `ssNodePairsQExp`.
--
--   The specialisation data are: an automorphism $\theta$ of $F_M$ over $\overline{\mathbb{Q}}$; an algebra homomorphism $\alpha : F_{M/p} \to F_M$, integral by `hα`, with $\beta := \theta \circ \alpha$ integral by `hβ`; a place specialisation $\mathrm{Psp} =$ `JHPlaceSpecialization p M H hpM A`, whose component `sp` sends places of $F_{M/p}$ to places of $\bar F$; and a prolongation datum $\mathrm{Rpd}$ for $\mathrm{Psp}$ and $\theta$, providing two regular prolongations $R_1, R_2$ of $A$ in $F_M$ with residue maps to $\bar F$. For a place $W$ of $F_M$ one has $\mathrm{reduceFst}\,W = \mathrm{sp}(W|_\alpha)$ and $\mathrm{reduceSnd}\,W = \delta(\mathrm{sp}(W|_\beta))$, where $W|_\varphi$ denotes restriction along $\varphi$; $W$ is `IsStrictFst` when $\delta(\mathrm{Frob}(\mathrm{reduceFst}\,W)) = \mathrm{reduceSnd}\,W$ and $\mathrm{reduceFst}\,W$ is not `Fixed` for $\delta$, and `IsStrictSnd` when $\mathrm{reduceFst}\,W = \mathrm{Frob}(\mathrm{reduceSnd}\,W)$ and $\mathrm{reduceSnd}\,W$ is not `Fixed` for $\delta$, with $\mathrm{Frob} =$ `qExpFrobeniusPlaceModL κ (ΓN p M H hpM) p`.
--
--   The structural hypotheses are the following. `hwgen`: for any two $\overline{\mathbb{Q}}$-sections $y, y'$ of $\mathfrak{X}.\mathrm{Meta}.\mathrm{toBase}$, if $y'$ followed by $\mathfrak{X}.\mathrm{eeta}$, the first pullback projection and $\mathfrak{X}.w.\mathrm{hom}$ agrees with $y$ followed by $\mathfrak{X}.\mathrm{eeta}$ and the first projection, then the place of $y'$ is the image of the place of $y$ under the semilinear automorphism `SemilinearAut.ofAlgAut θ`. `hα_coe`: $\alpha$ is the identity on Laurent expansions. `hβ_coe`: $\beta = \theta \circ \alpha$ acts on Laurent expansions by `qExpand (AlgebraicClosure ℚ) p`. `hTD`: the type dichotomy, that for every place $W$ of $F_M$ either $\mathrm{reduceFst}\,W = \mathrm{Frob}(\mathrm{reduceSnd}\,W)$ or $\delta(\mathrm{Frob}(\mathrm{reduceFst}\,W)) = \mathrm{reduceSnd}\,W$. `hmodel`: $\mathrm{Rpd}$ is a model for $(\alpha,\beta,\delta)$, i.e. the two divisor laws and the two cusp laws of `IsModel` hold. `hcompat` and `hcompat'`: for each $i \in \{0,1\}$, each section $y$ as above, each $A$-point $u$ over $\operatorname{Spec}\rho$ with $\mathrm{barPt}\,A$ followed by $u$ equal to $y$ followed by $\mathfrak{X}.\mathrm{eeta}$ and the first projection, each $\kappa$-point $u_\kappa$ of the fibre at `(residue A).comp ρ` reducing $u$ and splitting the second projection, and each closed point $P_0$ of $(\mathfrak{X}.\mathrm{Mfib}\ A\ hA\ \rho\ h\rho).C$ whose image under $\mathfrak{X}.\mathrm{efib}$ followed by the $i$-th component map is the closed point of $u_\kappa$: the place of $P_0$ in the special fibre model equals $\mathrm{reduceFst}$ of the place of $y$ when $i = 0$ and $\mathrm{reduceSnd}$ of the place of $y$ otherwise (`hcompat`), while (`hcompat'`) for $i = 0$ one has $\mathrm{reduceSnd}$ of the place of $y$ equal to $\delta(\mathrm{Frob}$ of the place of $P_0)$, and for $i = 1$ one has $\mathrm{reduceFst}$ of the place of $y$ equal to $\mathrm{Frob}$ of the place of $P_0$. `hO`: the order law at $\delta$-fixed affine places (`OrderLawFixed`). `hRL`: the regularity law for $\mathrm{Rpd}$ relative to $SS$. `hNV`: the node value law for $\mathrm{Rpd}$ relative to $SS$. `hθgal`: $\theta$ commutes with the arithmetic Galois action of $\operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ on $F_M$.
--
--   Finally, a node pair $s \in SS$ is fixed (`hs`), together with a positive integer $es$ (`hes`) and an annulus datum $\mathrm{An} :$ [`AlgebraicCurve.Annulus A F_M`](def/AlgebraicCurve_SemistableCharts.html#L86): a set $\mathrm{An.dom}$ of places of $F_M$, a parameter $\mathrm{An.param} \in F_M$ and a modulus $\mathrm{An.modulus}$ in the maximal ideal of $A$, satisfying the axioms of that structure (each place of the domain is rational, the parameter lies in its valuation ring and its value is a nonzero element of the maximal ideal dividing the modulus; every admissible value is attained by a unique place of the domain; the parameter minus its value has order $1$ at each place of the domain; and a function without zeros or poles on the domain admits a constant $c$ and an integer $m$ making its value times $c^{-1}$ times the $(-m)$-th power of the value of the parameter a unit of $A$ at every place of the domain). The hypotheses on this datum are: `hdom`, that $\mathrm{An.dom}$ consists exactly of the places $W$ with $\mathrm{reduceFst}\,W = s_1$ which are neither `IsStrictFst` nor `IsStrictSnd`; `hmodulus`, that $\mathrm{An.modulus} = p^{es} \cdot u$ for some unit $u$ of $A$; `hinert`, that $\mathrm{An.param}$ is fixed by the arithmetic Galois action of every element of the inertia subgroup of $A$ over $\mathbb{Q}$; `hz₁`, that $\mathrm{An.modulus}^{-1} \cdot \mathrm{An.param}$ lies in $R_1$'s integers; `hz₂`, that $\mathrm{An.param}$ lies in $R_2$'s integers with nonzero residue; `hatt₂`, that $\mathrm{An.param}$ lies in $R_2$'s integers with $\operatorname{ord}_{s_2}$ of its residue equal to $1$, and that for every $f$ in $R_2$'s integers with nonzero residue and with $\operatorname{ord}_P f = 0$ for all $P \in \mathrm{An.dom}$, the element $(\mathrm{evalAt}_P f) \cdot (\mathrm{evalAt}_P \mathrm{An.param})^{-\operatorname{ord}_{s_2}(\text{residue of } f)}$ lies in $A$ and is a unit there, for every $P \in \mathrm{An.dom}$; and `hatt₁`, the same two assertions for $R_1$, $s_1$ and the function $\mathrm{An.modulus} \cdot \mathrm{An.param}^{-1}$ in place of $\mathrm{An.param}$.
--
--   The configuration consists of a finitely supported function $E$ from places of $F_M$ to $\mathbb{Z}$ supported in $\mathrm{An.dom}$ (`hE`) and with $E(V) \ge 0$ for all $V$ (`hE0`), an integer $m$, and a unit $u$ of $A$ satisfying the leading law `hlead`:
--   $$u \cdot \mathrm{An.modulus}^{m} = \prod_{V} \bigl(-\mathrm{evalAt}_V(\mathrm{An.param})\bigr)^{E(V)}$$
--   in $\overline{\mathbb{Q}}$, the product being `E.prod`.
--
--   Under these hypotheses there exists $g \in F_M$ with the following four properties: $g$ lies in $R_1$'s integers, its $R_1$-residue is nonzero and $\operatorname{ord}_{s_1}$ of that residue equals $m$; $g$ lies in $R_2$'s integers, its $R_2$-residue is nonzero and $\operatorname{ord}_{s_2}$ of that residue equals $\bigl(\sum_V E(V)\bigr) - m$; for every place $V$ of $F_M$ such that $\mathrm{reduceFst}\,V = t_1$ for some $t \in SS$ and $V$ is neither `IsStrictFst` nor `IsStrictSnd`, one has $\operatorname{ord}_V g = E(V)$; and for every place $V$ with $\operatorname{ord}_V g \ne 0$ which is neither `IsStrictFst` nor `IsStrictSnd`, there is $t \in SS$ with $\mathrm{reduceFst}\,V = t_1$.
--
--   This is the effective placement step in the analysis of the two-component special fibre of the Deligne–Rapoport model of $X_H(M)$ at a prime $p$ exactly dividing $M$: on a single supersingular node annulus it produces a function of $F_M$ whose divisor on the annulus is a prescribed effective configuration and whose residues on the two branches have prescribed orders at the node, the split of orders between the branches being governed by the leading law. It is cited by the corresponding statement for balanced (signed) configurations, [`ModularCurve.XHDRModelAtP.exists_ord_eq_and_smul_mem_integers_of_isUnit_mul_modulus_zpow_eq_prod_neg_evalAt_zpow_of_annulus_offDiag_of_wgen`](thm.html#ModularCurve.XHDRModelAtP.exists_ord_eq_and_smul_mem_integers_of_isUnit_mul_modulus_zpow_eq_prod_neg_evalAt_zpow_of_annulus_offDiag_of_wgen), which obtains the general case by dividing two such placements.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_exists_ord_residue_eq_and_ord_eq_of_nonneg_of_isUnit_mul_modulus_zpow_eq_prod_neg_evalAt_zpow_of_annulus_offDiag_of_wgen.lean

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

theorem ModularCurve.XHDRModelAtP.exists_ord_residue_eq_and_ord_eq_of_nonneg_of_isUnit_mul_modulus_zpow_eq_prod_neg_evalAt_zpow_of_annulus_offDiag_of_wgen
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

    (s : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) ×
      Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) (hs : s ∈ SS)
    (es : ℕ) (hes : 0 < es) (An : AlgebraicCurve.Annulus A ↥(xHFunctionFieldBar M H))
    (hdom : ∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
      W ∈ An.dom ↔ (Psp.reduceFst α hα W = s.1 ∧ ¬ Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W ∧ ¬ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ W))
    (hmodulus : ∃ u : ↥A, IsUnit u ∧ An.modulus = ((p : ℕ) : ↥A) ^ es * u)
    (hinert : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.inertiaSubgroupIn ℚ →
      (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • An.param = An.param)
    (hz₁ : algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((An.modulus : AlgebraicClosure ℚ))⁻¹ * An.param ∈ Rpd.R₁.integers)
    (hz₂ : ∃ h₂ : An.param ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨An.param, h₂⟩ ≠ 0)
    (hatt₂ : ∃ h₂ : An.param ∈ Rpd.R₂.integers, s.2.ord (Rpd.R₂.residue ⟨An.param, h₂⟩) = 1 ∧
      ∀ (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨f, hf⟩ ≠ 0 →
        (∀ P ∈ An.dom, P.ord f = 0) → ∀ P ∈ An.dom,
          ∃ h : P.evalAt f * (P.evalAt An.param) ^ (-(s.2.ord (Rpd.R₂.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A))
    (hatt₁ : ∃ h₁ : algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((An.modulus : ↥A) : AlgebraicClosure ℚ) * An.param⁻¹ ∈ Rpd.R₁.integers,
      s.1.ord (Rpd.R₁.residue ⟨_, h₁⟩) = 1 ∧
      ∀ (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨f, hf⟩ ≠ 0 →
        (∀ P ∈ An.dom, P.ord f = 0) → ∀ P ∈ An.dom,
          ∃ h : P.evalAt f * (P.evalAt (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((An.modulus : ↥A) : AlgebraicClosure ℚ) * An.param⁻¹)) ^
            (-(s.1.ord (Rpd.R₁.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A))

    (E : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) →₀ ℤ) (hE : ∀ V, E V ≠ 0 → V ∈ An.dom)
    (hE0 : ∀ V, 0 ≤ E V)
    (m : ℤ) (u : ↥A) (hu : IsUnit u)
    (hlead : ((u : ↥A) : AlgebraicClosure ℚ) * ((An.modulus : ↥A) : AlgebraicClosure ℚ) ^ m
      = E.prod (fun V n => (-(V.evalAt An.param)) ^ n)) :
    ∃ g : ↥(xHFunctionFieldBar M H),
      (∃ h₁ : g ∈ Rpd.R₁.integers, Rpd.R₁.residue ⟨g, h₁⟩ ≠ 0 ∧ s.1.ord (Rpd.R₁.residue ⟨g, h₁⟩) = m) ∧
      (∃ h₂ : g ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨g, h₂⟩ ≠ 0 ∧
        s.2.ord (Rpd.R₂.residue ⟨g, h₂⟩) = (E.sum fun _ n => n) - m) ∧
      (∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
        (∃ t ∈ SS, Psp.reduceFst α hα V = t.1) → ¬ Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ V → ¬ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ V → V.ord g = E V) ∧
      (∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
        V.ord g ≠ 0 → ¬ Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ V → ¬ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ V → ∃ t ∈ SS, Psp.reduceFst α hα V = t.1) := by sorry
