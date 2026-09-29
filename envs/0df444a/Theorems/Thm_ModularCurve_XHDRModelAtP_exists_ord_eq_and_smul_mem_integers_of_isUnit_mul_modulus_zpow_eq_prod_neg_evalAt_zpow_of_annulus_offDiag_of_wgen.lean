-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_exists_ord_eq_and_smul_mem_integers_of_isUnit_mul_modulus_zpow_eq_prod_neg_evalAt_zpow_of_annulus_offDiag_of_wgen
-- name    : ModularCurve.XHDRModelAtP.exists_ord_eq_and_smul_mem_integers_of_isUnit_mul_modulus_zpow_eq_prod_neg_evalAt_zpow_of_annulus_offDiag_of_wgen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/88881347-24d5-5ac9-88f6-a958a8f8b430
-- title:
--   Balanced configurations on a supersingular node annulus are principal
-- statement:
--   Throughout, $p$ is a prime and $M$ a positive integer with $p \mid M$ and $p^2 \nmid M$ (hypotheses `hpM`, `hpM2`), $H$ is a subgroup of $(\mathbb Z/M)^\times$ which contains the kernel of the reduction map $(\mathbb Z/M)^\times \to (\mathbb Z/(M/p))^\times$ (hypothesis `hHp`), $M/p$ is nonzero, `hj` asserts that the $q$-expansion `jqModC ℚ` of $j$ lies in the full-level $q$-expansion function field `qExpFunctionFieldC ℚ ⊤`, and $\mathfrak X$ is a model datum of type `XHDRModelAtP p M H hpM hj` (an integral model of $X_H(M)$ over `R p` together with its curve model `𝔛.Meta` of the geometric function field $F_M =$ `xHFunctionFieldBar M H`, the identification `𝔛.eeta` of `𝔛.Meta.C` with the geometric generic fibre, the involution `𝔛.w`, and the fibre data `𝔛.Mfib`, `𝔛.efib`, `𝔛.comp`).
--
--   Reduction data. $A$ is a valuation subring of $\overline{\mathbb Q}$ with $p$ a non-unit of $A$ (`hA`), whose residue field $\kappa$ has characteristic $p$ and is algebraically closed, and $\rho :$ `R p` $\to A$ is a ring homomorphism whose composite with the inclusion $A \subset \overline{\mathbb Q}$ is the structure map `algebraMap (R p) (AlgebraicClosure ℚ)` (`hρ`). Write $F_{M/p} =$ `xHFunctionFieldBar (M/p) (infSubgroup p M H hpM)`, where `infSubgroup` is the image of $H$ in $(\mathbb Z/(M/p))^\times$, and $\bar F =$ `JHNeronObjectAtP.Fbar p M H hpM κ`, the mod-$p$ $q$-expansion function field `qExpFunctionFieldC κ (ΓN p M H hpM)`. Further, `pb` is a unit of $\mathbb Z/(M/p)$ whose underlying residue is $p$ (`hpb`), and $\delta$ is a self-map of the set of places of $\bar F$ over $\kappa$ which, by `hδ`, acts as the semilinear automorphism attached to the diamond automorphism `diamondActionModL κ (M/p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M/p) pb)`. The finite set $SS$ of pairs of places of $\bar F$ is characterised by `hSS` as the set of supersingular node pairs `ssNodePairsQExp κ (ΓN p M H hpM) p`, that is, the pairs $s$ with $s_2$ in `ssPlacesQExp` and $s_1 =$ `qExpFrobeniusPlaceModL κ (ΓN p M H hpM) p` $s_2$, the restriction of $s_2$ along the $p$-power Frobenius of the mod-$p$ $q$-expansion field.
--
--   Correspondence and specialisation data. $\theta$ is an automorphism of $F_M$ over $\overline{\mathbb Q}$, $\alpha : F_{M/p} \to F_M$ an $\overline{\mathbb Q}$-algebra map that is integral (`hα`), and $\beta = \theta \circ \alpha$ is likewise integral (`hβ`); `hα_coe` says that $\alpha$ does not change Laurent series, while `hβ_coe` says that the Laurent series of $\beta(u)$ is `qExpand (AlgebraicClosure ℚ) p` applied to that of $u$, i.e. $q \mapsto q^p$. `Psp` is a place-specialisation datum of type `JHPlaceSpecialization p M H hpM A`, with specialisation map `Psp.sp` from places of $F_{M/p}$ to places of $\bar F$; for a place $W$ of $F_M$ one writes `Psp.reduceFst α hα` $W =$ `Psp.sp` of the restriction of $W$ along $\alpha$, and `Psp.reduceSnd β hβ δ` $W = \delta($`Psp.sp` of the restriction of $W$ along $\beta)$. The predicate `Psp.IsStrictFst` holds at $W$ when $\delta$ of the Frobenius of the first reduction equals the second reduction and the first reduction is not `Fixed` for $\delta$; `Psp.IsStrictSnd` holds at $W$ when the first reduction equals the Frobenius of the second reduction and the second reduction is not `Fixed` for $\delta$. `Rpd` is a prolongation datum of type `JHPlaceSpecialization.ProlongationDatum Psp θ`, providing two regular prolongations `Rpd.R₁`, `Rpd.R₂` of $A$ in $F_M$ with residue maps to $\bar F$.
--
--   The following hypotheses link these data (their content is summarised here, each being used as stated). `hwgen`: for sections $y, y'$ of `𝔛.Meta.toBase`, if $y'$ followed by `𝔛.eeta`, the first pullback projection and `𝔛.w.hom` equals $y$ followed by `𝔛.eeta` and the first projection, then the place of $y'$ is the image of the place of $y$ under the semilinear automorphism attached to $\theta$. `hθgal`: $\theta$ commutes with the arithmetic Galois action of $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ on $F_M$. `hTD` is the type dichotomy: every place $W$ of $F_M$ satisfies either first reduction $=$ Frobenius of second reduction, or $\delta($Frobenius of first reduction$) =$ second reduction. `hmodel` asserts `Rpd.IsModel α β hα hβ δ`, the conjunction of the two divisor laws and the two cusp laws at $\infty$ and at $0$. `hcompat` and `hcompat'` are two compatibilities between the special fibre and the two reductions: for $i \in \{0,1\}$, a section $y$ of `𝔛.Meta.toBase`, an $A$-point $u$ of the integral model over `Spec.map ρ` whose base change along $A \subset \overline{\mathbb Q}$ is the point determined by $y$, a $\kappa$-point $u_\kappa$ of the fibre of `toBase p (ΓM M H) hj` along `residue ∘ ρ` lifting $u$ and lying over the identity, and a closed point $P_0$ of `(𝔛.Mfib A hA ρ hρ).C` whose image under `𝔛.efib` followed by the $i$-th component map `𝔛.comp` is the closed point of $u_\kappa$: the place of $P_0$ equals `Psp.reduceFst α hα` of the place of $y$ if $i = 0$, and `Psp.reduceSnd β hβ δ` of the place of $y$ otherwise (`hcompat`); and, with the same quantifiers, the second reduction of the place of $y$ equals $\delta$ of the Frobenius of the place of $P_0$ when $i = 0$, while the first reduction of the place of $y$ equals the Frobenius of the place of $P_0$ when $i = 1$ (`hcompat'`). Finally `hO`, `hRL` and `hNV` are the order law at $\delta$-fixed places (`Rpd.OrderLawFixed`), the regularity law (`Rpd.RegularityLaw`, relative to $SS$) and the node value law (`Rpd.NodeValueLaw`, relative to $SS$), each formulated for functions lying in both `Rpd.R₁.integers` and `Rpd.R₂.integers` with nonzero residues.
--
--   Annulus data. A pair $s = (s_1, s_2) \in SS$ is fixed, together with a positive natural number $e_s$ and an annulus `An` of type [`AlgebraicCurve.Annulus A F_M`](def/AlgebraicCurve_SemistableCharts.html#L86), i.e. a set `An.dom` of places of $F_M$ over $\overline{\mathbb Q}$, a parameter `An.param` $\in F_M$ and a modulus `An.modulus` in the maximal ideal of $A$, subject to the annulus axioms: every place of the domain is rational, holds the parameter in its valuation ring, the value of the parameter lies in the maximal ideal of $A$, is nonzero and divides the modulus by an element of the maximal ideal; conversely each such value is attained by exactly one place of the domain; the parameter minus its value has order $1$ at each place of the domain; and a unit principle holds for functions with order $0$ throughout the domain. The hypotheses on `An` are: `hdom`, that a place $W$ lies in `An.dom` precisely when `Psp.reduceFst α hα` $W = s_1$ and $W$ satisfies neither `Psp.IsStrictFst` nor `Psp.IsStrictSnd`; `hmodulus`, that `An.modulus` $= p^{e_s} u$ for some unit $u$ of $A$; `hinert`, that the arithmetic Galois action of every $\sigma$ in the inertia subgroup `A.inertiaSubgroupIn ℚ` fixes `An.param`; `hz₁`, that $\pi^{-1} z$ lies in `Rpd.R₁.integers`, where $z =$ `An.param` and $\pi$ is the image of `An.modulus` in $\overline{\mathbb Q}$; `hz₂`, that $z$ lies in `Rpd.R₂.integers` with nonzero `Rpd.R₂`-residue; `hatt₂`, that $z$ lies in `Rpd.R₂.integers`, that its residue has order $1$ at $s_2$, and that for every $f \in$ `Rpd.R₂.integers` with nonzero residue and with $\mathrm{ord}_P f = 0$ for all $P \in$ `An.dom`, the element $f(P) \cdot z(P)^{-m}$, with $m$ the order at $s_2$ of the residue of $f$, lies in $A$ and is a unit there, for every $P \in$ `An.dom`; and `hatt₁`, the corresponding statement for the element $\pi z^{-1}$ in place of $z$, for `Rpd.R₁` and for the place $s_1$.
--
--   Balanced configuration. $E$ is a finitely supported $\mathbb Z$-valued function on the places of $F_M$ over $\overline{\mathbb Q}$, supported in `An.dom` (`hE`), and there are an integer $d$ and a unit $u$ of $A$ with
--   $$u \cdot \pi^{d} = \prod_{V} \bigl(-V(\mathrm{An.param})\bigr)^{E(V)}$$
--   in $\overline{\mathbb Q}$, the product being over the support of $E$ and $V(\cdot)$ denoting evaluation `Place.evalAt` at $V$ (hypothesis `hbal`).
--
--   Conclusion. Under these hypotheses there exists $f \in F_M$ such that: (i) $f \neq 0$; (ii) for every place $V$ of $F_M$ over $\overline{\mathbb Q}$ such that `Psp.reduceFst α hα` $V$ is the first coordinate of some pair of $SS$ and $V$ satisfies neither `Psp.IsStrictFst` nor `Psp.IsStrictSnd`, one has $\mathrm{ord}_V f = E(V)$; (iii) for every place $V$ with $\mathrm{ord}_V f \neq 0$ satisfying neither `Psp.IsStrictFst` nor `Psp.IsStrictSnd`, there is a pair in $SS$ whose first coordinate is `Psp.reduceFst α hα` $V$; and (iv) there is $c \in \overline{\mathbb Q}$ such that $c \cdot f$ lies in `Rpd.R₁.integers` with nonzero `Rpd.R₁`-residue and also in `Rpd.R₂.integers` with nonzero `Rpd.R₂`-residue.
--
--   This is the annulus-clearing step in the geometric analysis of the Deligne–Rapoport type model of $X_H(M)$ at a prime $p$ exactly dividing $M$: a configuration on the node annulus of one supersingular pair satisfying the balance relation between the modulus and the parameter values is realised by a global function, with no order outside the supersingular annuli, and normalisable to have nonzero residues on both components of the special fibre. It feeds the construction of good divisor classes in [`ModularCurve.XHDRModelAtP.isGoodClass_of_forall_dvd_ord_residue_of_annulus_offDiag_of_wgen`](thm.html#ModularCurve.XHDRModelAtP.isGoodClass_of_forall_dvd_ord_residue_of_annulus_offDiag_of_wgen), and is obtained from the corresponding statement for non-negative configurations with prescribed residue orders.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_exists_ord_eq_and_smul_mem_integers_of_isUnit_mul_modulus_zpow_eq_prod_neg_evalAt_zpow_of_annulus_offDiag_of_wgen.lean

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

theorem ModularCurve.XHDRModelAtP.exists_ord_eq_and_smul_mem_integers_of_isUnit_mul_modulus_zpow_eq_prod_neg_evalAt_zpow_of_annulus_offDiag_of_wgen
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
    (d : ℤ) (u : ↥A) (hu : IsUnit u)
    (hbal : ((u : ↥A) : AlgebraicClosure ℚ) * ((An.modulus : ↥A) : AlgebraicClosure ℚ) ^ d
      = E.prod (fun V m => (-(V.evalAt An.param)) ^ m)) :
    ∃ f : ↥(xHFunctionFieldBar M H), f ≠ 0 ∧
      (∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
        (∃ t ∈ SS, Psp.reduceFst α hα V = t.1) → ¬ Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ V → ¬ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ V → V.ord f = E V) ∧
      (∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
        V.ord f ≠ 0 → ¬ Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ V → ¬ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ V → ∃ t ∈ SS, Psp.reduceFst α hα V = t.1) ∧
      (∃ c : AlgebraicClosure ℚ,
        (∃ h₁ : c • f ∈ Rpd.R₁.integers, Rpd.R₁.residue ⟨c • f, h₁⟩ ≠ 0) ∧
        (∃ h₂ : c • f ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨c • f, h₂⟩ ≠ 0)) := by sorry
