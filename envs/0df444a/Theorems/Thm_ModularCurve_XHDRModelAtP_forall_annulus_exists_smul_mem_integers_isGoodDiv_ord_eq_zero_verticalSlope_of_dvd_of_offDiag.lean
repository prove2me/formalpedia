-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_forall_annulus_exists_smul_mem_integers_isGoodDiv_ord_eq_zero_verticalSlope_of_dvd_of_offDiag
-- name    : ModularCurve.XHDRModelAtP.forall_annulus_exists_smul_mem_integers_isGoodDiv_ord_eq_zero_verticalSlope_of_dvd_of_offDiag
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/c50fb3b3-7563-5a67-a394-418ef1593c4f
-- title:
--   Vertical-slope functions on the node annuli at p ∥ M
-- statement:
--   Throughout, $p$ is a prime and $M$ a positive integer, $H \le (\mathbb{Z}/M)^\times$ a subgroup, and the level hypotheses are: $p \mid M$ (`hpM`), $p^2 \nmid M$ (`hpM2`), and `hHp`, which requires every unit $u$ of $\mathbb{Z}/M$ whose image under `ZMod.unitsMap` for the divisibility $(M/p) \mid M$ is $1$ to lie in $H$; $M/p$ is non-zero. The hypothesis `hj` says that the $q$-series $j$ of `jqModC` lies in `qExpFunctionFieldC ℚ ⊤`, the function field at full level, and $\mathfrak{X}$ is a term of the integral-model structure `XHDRModelAtP p M H hpM hj` for $X_H(M)$ over `R p`, carrying in particular a curve model $\mathfrak{X}.\mathrm{Meta}$ of $F :=$ `xHFunctionFieldBar M H` (the base change to $\overline{\mathbb{Q}}$ of the level-$(M,H)$ $q$-expansion function field) over $\overline{\mathbb{Q}}$, the comparison $\mathfrak{X}.\mathrm{eeta}$ with the generic fibre, and the involution $\mathfrak{X}.w$.
--
--   The place data consist of a valuation subring $A$ of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $A$ (`hA`, the meaning of `LiesOverPrime`), whose residue field $\kappa$ has characteristic $p$ and is algebraically closed, together with a ring map $\rho :$ `R p` $\to A$ such that $\rho$ followed by the inclusion $A \hookrightarrow \overline{\mathbb{Q}}$ is the structure map `R p` $\to \overline{\mathbb{Q}}$ (`hρ`). Write $\bar F :=$ `JHNeronObjectAtP.Fbar p M H hpM κ`, the function field of level `ΓN p M H hpM` over $\kappa$.
--
--   The diamond data consist of a unit $\bar p$ of $\mathbb{Z}/(M/p)$ reducing to $p$ (`hpb`) and a self-map $\delta$ of the set of places of $\bar F$ over $\kappa$ such that $\delta v$ is the translate of $v$ by the semilinear automorphism attached to the diamond automorphism `diamondActionModL` at level $M/p$ and subgroup `infSubgroup p M H hpM` (the image of $H$) evaluated at a $\Gamma_0(M/p)$-lift of $\bar p$ (`hδ`). The finite set $SS$ of pairs of places of $\bar F$ is required (`hSS`) to consist exactly of the members of `ssNodePairsQExp κ (ΓN p M H hpM) p`, i.e. of the pairs $s$ whose second entry is a supersingular place and whose first entry is the mod-$p$ Frobenius pull-back `qExpFrobeniusPlaceModL` of the second.
--
--   The transport and specialisation data consist of: an automorphism $\theta$ of $F$ over $\overline{\mathbb{Q}}$; an algebra map $\alpha$ from `xHFunctionFieldBar (M/p) (infSubgroup p M H hpM)` to $F$ over $\overline{\mathbb{Q}}$, integral (`hα`), such that $\beta$, meaning $\alpha$ followed by $\theta$, is integral as well (`hβ`); a specialisation packet $P :=$ `Psp` of type `JHPlaceSpecialization p M H hpM A`, which supplies a surjective map $\mathrm{sp}$ from places of the level-$(M/p)$ field to places of $\bar F$ together with its divisor, inertia and Frobenius compatibilities and a map on degree-zero Picard groups; and a prolongation datum $R :=$ `Rpd` for $P$ and $\theta$, consisting of two regular prolongations $R_1, R_2$ of $A$ to $F$ with values in $\bar F$ (each a valuation subring `integers` of $F$ with a surjective residue map onto $\bar F$ whose kernel is the maximal ideal) linked by $f \in R_2.\mathrm{integers} \leftrightarrow \theta f \in R_1.\mathrm{integers}$ and $R_2.\mathrm{residue}(f) = R_1.\mathrm{residue}(\theta f)$. Here `reduceFst` $\alpha$ sends a place $W$ of $F$ to $\mathrm{sp}(W|_\alpha)$, `reduceSnd` $\beta$ sends $W$ to $\delta(\mathrm{sp}(W|_\beta))$; `Fixed` $\delta$ holds at $v$ when $\mathrm{Frob}(\delta(\mathrm{Frob}\, v)) = v$; $W$ is `IsStrictFst` when $\delta(\mathrm{Frob}(\mathrm{reduceFst}\,W)) = \mathrm{reduceSnd}\,W$ and `Fixed` fails at $\mathrm{reduceFst}\,W$, and `IsStrictSnd` when $\mathrm{reduceFst}\,W = \mathrm{Frob}(\mathrm{reduceSnd}\,W)$ and `Fixed` fails at $\mathrm{reduceSnd}\,W$. The hypotheses on these data are: `hwgen`, that for two $\overline{\mathbb{Q}}$-points $y, y'$ of $\mathfrak{X}.\mathrm{Meta}.C$ over the base, equality of $y'$ followed by `eeta`, the first projection and $\mathfrak{X}.w$ with $y$ followed by `eeta` and the first projection forces `pointEquivPlace` $y'$ to be the $\theta$-translate of `pointEquivPlace` $y$; `hα_coe`, that $\alpha$ does not change Laurent expansions; `hTD`, the type dichotomy, that for every place $W$ of $F$ either $\mathrm{reduceFst}\,W = \mathrm{Frob}(\mathrm{reduceSnd}\,W)$ or $\delta(\mathrm{Frob}(\mathrm{reduceFst}\,W)) = \mathrm{reduceSnd}\,W$; and `hmodel`, that $R$ is a model for $(\alpha, \beta, \delta)$, i.e. the two divisor laws and the cusp laws at $\infty$ and at $0$ hold.
--
--   Two fibre-reading compatibilities are imposed. Both are quantified over $i \in \{0,1\}$, a $\overline{\mathbb{Q}}$-point $y$ of $\mathfrak{X}.\mathrm{Meta}.C$ over the base, a morphism $u$ to the model over $\mathrm{Spec}\,\rho$ whose composite with the bar point of $A$ agrees with $y$ followed by `eeta` and the first projection, a $\kappa$-point $u_\kappa$ of the fibre over the residue map composed with $\rho$ which reduces $u$ and is a section, and a closed point $P_0$ of $(\mathfrak{X}.\mathrm{Mfib}\,A\,hA\,\rho\,h\rho).C$ lying over the closed point of $u_\kappa$ through `efib` followed by the $i$-th component `comp`. Under these conditions `hcompat` asserts that the place of $P_0$ in the fibre curve model is $P.\mathrm{reduceFst}\,\alpha$ of `pointEquivPlace` $y$ when $i = 0$ and $P.\mathrm{reduceSnd}\,\beta\,\delta$ of `pointEquivPlace` $y$ otherwise, while `hcompat'` asserts that for $i = 0$ one has $P.\mathrm{reduceSnd}\,\beta\,\delta(\text{pointEquivPlace } y) = \delta(\mathrm{Frob}(\text{place of } P_0))$ and otherwise $P.\mathrm{reduceFst}\,\alpha(\text{pointEquivPlace } y) = \mathrm{Frob}(\text{place of } P_0)$, with $\mathrm{Frob} =$ `qExpFrobeniusPlaceModL κ (ΓN p M H hpM) p`.
--
--   Finally a width $e(s) \ge 1$ is prescribed for every $s \in SS$ (`e`, `he`).
--
--   The assertion is the following. Let $\mathcal{A}$ assign to every $s \in SS$ an annulus $\mathcal{A}_s$ of $F$ along $A$ in the sense of [`AlgebraicCurve.Annulus`](def/AlgebraicCurve_SemistableCharts.html#L86) (a set $\mathrm{dom}$ of places of $F$ over $\overline{\mathbb{Q}}$, a parameter $z_s \in F$ and a modulus $m_s$ in the maximal ideal of $A$, subject to the axioms of that structure: rationality of the places of $\mathrm{dom}$, the divisibility $m_s = z_s(P)\cdot(\text{element of the maximal ideal})$ with $z_s(P)$ a non-zero element of the maximal ideal, unique solvability of $z_s(P) = c$ for admissible $c$, $\mathrm{ord}_P(z_s - z_s(P)) = 1$, and the unit principle for functions without zeros or poles on $\mathrm{dom}$). Assume that for every $s \in SS$ the following seven clauses hold:
--
--   (i) a place $W$ of $F$ lies in $\mathrm{dom}\,\mathcal{A}_s$ if and only if $P.\mathrm{reduceFst}\,\alpha\,W$ equals the first entry of $s$ and $W$ is neither `IsStrictFst` nor `IsStrictSnd`;
--
--   (ii) $m_s = p^{e(s)}u$ for some unit $u$ of $A$;
--
--   (iii) $z_s$ is fixed by the `arithmeticGalois` action of every $\sigma$ in the inertia subgroup `A.inertiaSubgroupIn ℚ`;
--
--   (iv) $m_s^{-1}z_s$ lies in $R_1.\mathrm{integers}$;
--
--   (v) $z_s$ lies in $R_2.\mathrm{integers}$ and its $R_2$-residue is non-zero;
--
--   (vi) $z_s$ lies in $R_2.\mathrm{integers}$, the order of its $R_2$-residue at the second entry of $s$ is $1$, and for every $f \in R_2.\mathrm{integers}$ with non-zero $R_2$-residue and $\mathrm{ord}_P f = 0$ for all $P \in \mathrm{dom}\,\mathcal{A}_s$, and every such $P$, the value $f(P)\cdot z_s(P)^{-\mathrm{ord}_{s_2}(R_2.\mathrm{residue}\,f)}$ lies in $A$ and is a unit there;
--
--   (vii) $m_s z_s^{-1}$ lies in $R_1.\mathrm{integers}$, the order of its $R_1$-residue at the first entry of $s$ is $1$, and for every $f \in R_1.\mathrm{integers}$ with non-zero $R_1$-residue and $\mathrm{ord}_P f = 0$ for all $P \in \mathrm{dom}\,\mathcal{A}_s$, and every such $P$, the value $f(P)\cdot\bigl((m_s z_s^{-1})(P)\bigr)^{-\mathrm{ord}_{s_1}(R_1.\mathrm{residue}\,f)}$ lies in $A$ and is a unit there.
--
--   Then for every natural number $k$ divisible by all the widths $e(s)$, $s \in SS$, there exist $f \in F$ and $c \in \overline{\mathbb{Q}}$ with $c \cdot f \in R_1.\mathrm{integers}$ such that:
--
--   (1) $f \ne 0$;
--
--   (2) the $R_1$-residue of $c\cdot f$ is non-zero;
--
--   (3) every divisor $G$ on the places of $F$ whose coefficient at each place $V$ is $\mathrm{ord}_V f$ is a good divisor for $(\alpha, \beta, \delta)$, that is, every place in the support of $G$ is `IsStrictFst` or `IsStrictSnd`;
--
--   (4) $\mathrm{ord}_V f = 0$ for every place $V$ of $F$ such that `Fixed` $\delta$ holds at $P.\mathrm{reduceFst}\,\alpha\,V$ and $P.\mathrm{reduceFst}\,\alpha\,V$ differs from $s$ for every $s \in SS$;
--
--   (5) $\mathrm{ord}_v$ of the $R_1$-residue of $c\cdot f$, viewed in $\bar F$, vanishes for every place $v$ of $\bar F$ at which `Fixed` $\delta$ holds and which differs from $s$ for every $s \in SS$;
--
--   (6) for every $s \in SS$ there is a non-zero $a \in \overline{\mathbb{Q}}$ such that for every $P \in \mathrm{dom}\,\mathcal{A}_s$ one has $\mathrm{ord}_P f = 0$ and $f(P)\, a\, z_s(P)^{-k/e(s)}$ lies in $A$ and is a unit there, the exponent being the natural-number quotient $k/e(s)$ cast to $\mathbb{Z}$.
--
--   This is the construction, on the Deligne–Rapoport integral model of $X_H(M)$ at a prime $p$ exactly dividing $M$, of a function whose valuation varies with constant slope $k/e(s)$ across every supersingular node annulus, whose divisor is supported on strict places, and which has no zeros or poles at the remaining $\delta$-fixed places; the normalisation $c\cdot f$ is a unit of the first prolongation with prescribed residual behaviour. It feeds the off-diagonal computation of the component group of the Jacobian in [`ModularCurve.XHDRModelAtP.exists_jHPlaceSpecialization_prolongationDatum_gluedSpecialization_componentGroup_offDiag_of_wgen`](thm.html#ModularCurve.XHDRModelAtP.exists_jHPlaceSpecialization_prolongationDatum_gluedSpecialization_componentGroup_offDiag_of_wgen).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_forall_annulus_exists_smul_mem_integers_isGoodDiv_ord_eq_zero_verticalSlope_of_dvd_of_offDiag.lean

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

theorem ModularCurve.XHDRModelAtP.forall_annulus_exists_smul_mem_integers_isGoodDiv_ord_eq_zero_verticalSlope_of_dvd_of_offDiag
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
    (e : ↥SS → ℕ) (he : ∀ s, 0 < e s) :

    ∀ An : ↥SS → AlgebraicCurve.Annulus A ↥(xHFunctionFieldBar M H),
      (∀ s : ↥SS, ((∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
            W ∈ (An s).dom ↔ (Psp.reduceFst α hα W = s.1.1 ∧ ¬ Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W ∧ ¬ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ W)) ∧
          (∃ u : ↥A, IsUnit u ∧ (An s).modulus = ((p : ℕ) : ↥A) ^ (e s) * u) ∧
          (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.inertiaSubgroupIn ℚ →
            (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • (An s).param = (An s).param) ∧
          algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (((An s).modulus : AlgebraicClosure ℚ))⁻¹ * (An s).param ∈ Rpd.R₁.integers ∧
          (∃ h₂ : (An s).param ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨(An s).param, h₂⟩ ≠ 0) ∧

          (∃ h₂ : (An s).param ∈ Rpd.R₂.integers, s.1.2.ord (Rpd.R₂.residue ⟨(An s).param, h₂⟩) = 1 ∧
            ∀ (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨f, hf⟩ ≠ 0 →
              (∀ P ∈ (An s).dom, P.ord f = 0) → ∀ P ∈ (An s).dom,
                ∃ h : P.evalAt f * (P.evalAt (An s).param) ^ (-(s.1.2.ord (Rpd.R₂.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A)) ∧
          (∃ h₁ : algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (((An s).modulus : ↥A) : AlgebraicClosure ℚ) * (An s).param⁻¹ ∈ Rpd.R₁.integers,
            s.1.1.ord (Rpd.R₁.residue ⟨_, h₁⟩) = 1 ∧
            ∀ (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨f, hf⟩ ≠ 0 →
              (∀ P ∈ (An s).dom, P.ord f = 0) → ∀ P ∈ (An s).dom,
                ∃ h : P.evalAt f * (P.evalAt (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (((An s).modulus : ↥A) : AlgebraicClosure ℚ) * (An s).param⁻¹)) ^
                  (-(s.1.1.ord (Rpd.R₁.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A)))) →
      ∀ k : ℕ, (∀ s : ↥SS, e s ∣ k) →
        ∃ (f : ↥(xHFunctionFieldBar M H)) (c : AlgebraicClosure ℚ) (hc : c • f ∈ Rpd.R₁.integers),
          f ≠ 0 ∧ Rpd.R₁.residue ⟨c • f, hc⟩ ≠ 0 ∧
          (∀ G : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), (∀ V, G V = V.ord f) → Psp.IsGoodDiv α (θ.toAlgHom.comp α) hα hβ δ G) ∧
          (∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ (Psp.reduceFst α hα V) →
            (∀ s ∈ SS, Psp.reduceFst α hα V ≠ s.1) → V.ord f = 0) ∧
          (∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v → (∀ s ∈ SS, v ≠ s.1) →
            v.ord (Rpd.R₁.residue ⟨c • f, hc⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) = 0) ∧
          (∀ s : ↥SS, ∃ a : AlgebraicClosure ℚ, a ≠ 0 ∧ ∀ P ∈ (An s).dom, P.ord f = 0 ∧
            ∃ h : P.evalAt f * a * (P.evalAt (An s).param) ^ (-((k / e s : ℕ) : ℤ)) ∈ A, IsUnit (⟨_, h⟩ : ↥A)) := by sorry
