-- Prove2me | Theorems.Thm_ModularCurve_JHPlaceSpecialization_exists_comp_depthCompLaw_of_principalLaw_of_annulusInf
-- name    : ModularCurve.JHPlaceSpecialization.exists_comp_depthCompLaw_of_principalLaw_of_annulusInf
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/88dc12a8-956c-55ef-b506-7de8e08587f4
-- title:
--   A depth component map for J_H(M) at p ∥ M
-- statement:
--   Setting. Fix a prime $p$ and a modulus $M$ with $p \mid M$ (`hpM`) but $p^2 \nmid M$ (`hpM2`), and a subgroup $H \le (\mathbb{Z}/M)^\times$ such that every unit $u$ of $\mathbb{Z}/M$ whose image under `ZMod.unitsMap` for the divisibility $(M/p) \mid M$ is $1$ already lies in $H$ (`hHp`); thus $H$ contains the kernel of reduction to level $M/p$. Fix a valuation subring $A$ of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` lying over $p$, in the sense that $p$ is a nonunit of $A$ (`hA`), whose residue field $\kappa =$ `ResidueField ↥A` has characteristic $p$ and is algebraically closed. Write $F_M =$ `xHFunctionFieldBar M H` for the base change to $\overline{\mathbb{Q}}$ of the level-$\Gamma_H(M)$ function field inside Laurent series, $F_{M/p} =$ `xHFunctionFieldBar (M/p) (infSubgroup p M H hpM)` for the corresponding field at level $M/p$ with $H$ replaced by its image `infSubgroup p M H hpM` under reduction of units, $\bar F =$ `Fbar p M H hpM κ` $=$ `qExpFunctionFieldC κ (ΓN p M H hpM)` for the $q$-expansion function field over $\kappa$ attached to the congruence subgroup `ΓN p M H hpM`, and $J_H(M) =$ `JH M H` $= \mathrm{Pic}^0$ of $F_M$ over $\overline{\mathbb{Q}}$.
--
--   The degeneracy and transport maps. $\theta$ is a $\overline{\mathbb{Q}}$-algebra automorphism of $F_M$, and $\alpha \colon F_{M/p} \to F_M$ a $\overline{\mathbb{Q}}$-algebra homomorphism, with $\alpha$ integral (`hα`) and $\theta \circ \alpha$ integral (`hβ`); throughout, the second map is $\beta = \theta \circ \alpha$. The hypothesis `hα_coe` states that $\alpha$ is the identity on underlying Laurent series: for every $u \in F_{M/p}$, the Laurent series of $\alpha u$ equals that of $u$.
--
--   The diamond operator. $pb$ is a unit of $\mathbb{Z}/(M/p)$ whose underlying element is $p$ (`hpb`). The map $\delta$ on places of $\bar F$ over $\kappa$ is required (`hδ`) to be the action of the semilinear automorphism `SemilinearAut.ofAlgAut` of the diamond automorphism `diamondActionModL κ (M/p) (infSubgroup p M H hpM)` evaluated at the $\Gamma_0(M/p)$-lift [`CuspForm.gammaLift (M/p) pb`](def/CuspForm_HeckeOperatorFormsGammaH.html#L36) of $pb$; that is, $\delta$ is the reduced diamond operator $\langle p \rangle$ on places.
--
--   The node set. $SS$ is a finite set of pairs of places of $\bar F$ over $\kappa$, and `hSS` requires it to consist exactly of the pairs in `ssNodePairsQExp κ (ΓN p M H hpM) p`, i.e. pairs $s$ with $s.2$ a supersingular place and $s.1$ the mod-$p$ Frobenius place `qExpFrobeniusPlaceModL` of $s.2$.
--
--   Specialisation data. $Psp$ is a specialisation datum `JHPlaceSpecialization p M H hpM A`: a surjective map `sp` from places of $F_{M/p}$ over $\overline{\mathbb{Q}}$ to places of $\bar F$ over $\kappa$, together with an induced additive map on degree-zero divisor classes, compatibility of pushed-forward divisors with $q$-expansions, the property that push-forwards of principal divisors are principal, invariance of `sp` under the inertia subgroup `A.inertiaSubgroupIn ℚ` (the image in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of $A$) acting through `arithmeticGalois`, Frobenius equivariance for $\sigma$ Frobenius at $p$, and compatibility of the map on classes with push-forward of divisors. $Rpd$ is a `ProlongationDatum` for $Psp$ and $\theta$: a pair $R_1, R_2$ of regular prolongations of $A$ to $F_M$ with residue map to $\bar F$, such that $q$-expansions integral over $A$ are $R_1$-integral with the expected residue, and $f \in R_2$-integers if and only if $\theta f \in R_1$-integers, the $R_2$-residue of $f$ being the $R_1$-residue of $\theta f$. For a place $W$ of $F_M$, `Psp.reduceFst α hα W` is `sp` applied to the restriction of $W$ along $\alpha$, and the predicates `Psp.IsStrictFst`, `Psp.IsStrictSnd` record the two one-sided crossing types: $\delta(\mathrm{Frob}(\mathrm{red}_1 W)) = \mathrm{red}_2 W$ with $\mathrm{red}_1 W$ not $\delta$-fixed, respectively $\mathrm{red}_1 W = \mathrm{Frob}(\mathrm{red}_2 W)$ with $\mathrm{red}_2 W$ not $\delta$-fixed, where a place $v$ is $\delta$-fixed when $\mathrm{Frob}(\delta(\mathrm{Frob}\, v)) = v$.
--
--   The structural laws. `hFix`: every supersingular place $y \in$ `ssPlacesQExp κ (ΓN p M H hpM) p` and its Frobenius image are $\delta$-fixed in the above sense. `hTD`: the type dichotomy, that for every place $W$ of $F_M$ either $\mathrm{red}_1 W = \mathrm{Frob}(\mathrm{red}_2 W)$ or $\delta(\mathrm{Frob}(\mathrm{red}_1 W)) = \mathrm{red}_2 W$. `hmodel`: the model law `Rpd.IsModel`, the conjunction of the two divisor laws and the two cusp laws for $\alpha$, $\beta$, $\delta$. `hO`: the order law at $\delta$-fixed affine places, that for $f$ lying in both rings of integers with nonzero residues, the push-forward along $\mathrm{red}_1$ of the divisor of $f$ at such a place $v$ is $\mathrm{ord}_v$ of the $R_1$-residue plus $\mathrm{ord}$ at $\delta(\mathrm{Frob}\, v)$ of the $R_2$-residue. `hreg` and `hnv`: the regularity law and the node-value law relative to $SS$, the former asserting non-negativity of residue orders and existence of common values at nodes for functions without poles over the relevant place, the latter asserting that at a node $s \in SS$ not met by the divisor of $f$ the two residues take a common nonzero value $c \in \kappa$ at $s.1$ and $s.2$. `hθgal`: $\theta$ commutes with the action of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ on $F_M$ through `arithmeticGalois`.
--
--   Widths and annuli. $e \colon SS \to \mathbb{N}$ with $e(s) > 0$ for all $s$ (`he`). The hypothesis `hAnn` requires, for every $s \in SS$, an annulus $An$ of $F_M$ along $A$ in the sense of [`AlgebraicCurve.Annulus`](def/AlgebraicCurve_SemistableCharts.html#L86) (a set `An.dom` of places, a parameter `An.param` $\in F_M$ and a modulus `An.modulus` in the maximal ideal of $A$, subject to the axioms of that structure: every place of the domain is rational, the parameter lies in its valuation ring with value a nonzero element of the maximal ideal dividing the modulus, such values are attained by exactly one place of the domain, the parameter minus its value has order $1$ at each place of the domain, and a unit principle for functions with no zeros or poles on the domain), satisfying seven further clauses: (i) a place $W$ lies in `An.dom` exactly when $\mathrm{red}_1 W = s.1$ and $W$ is neither of strict first nor of strict second type; (ii) `An.modulus` $= p^{e(s)} u$ for some unit $u$ of $A$; (iii) `An.param` is fixed by every $\sigma$ in the inertia subgroup `A.inertiaSubgroupIn ℚ` acting through `arithmeticGalois`; (iv) the image in $F_M$ of `An.modulus`$^{-1}$ times `An.param` lies in the $R_1$-integers; (v) `An.param` lies in the $R_2$-integers with nonzero $R_2$-residue; (vi) the $R_2$-residue of `An.param` has order $1$ at $s.2$, and for every $f$ in the $R_2$-integers with nonzero residue and with $\mathrm{ord}_P f = 0$ for all $P \in$ `An.dom`, at every such $P$ the product of $P$-evaluations $P(f) \cdot P(\mathrm{param})^{-\mathrm{ord}_{s.2}(\mathrm{res}_2 f)}$ lies in $A$ and is a unit there; (vii) the flipped parameter, the image of `An.modulus` times `An.param`$^{-1}$, lies in the $R_1$-integers, its $R_1$-residue has order $1$ at $s.1$, and the analogous unit statement holds for $f$ in the $R_1$-integers with the exponent $-\mathrm{ord}_{s.1}(\mathrm{res}_1 f)$.
--
--   Depths. `depth` is a function from places of $F_M$ over $\overline{\mathbb{Q}}$ to $\mathbb{N}$, and `hdepth` requires that for every $s \in SS$ and every annulus $An$ satisfying the same seven clauses just listed, the law `Psp.AnnulusDepthLawInf` holds for $s$, $An$ and `depth`: for every place $V$ of $F_M$ with $\mathrm{red}_1 V = s.1$ which is fixed by the inertia subgroup acting through `arithmeticGalois`, one has $v_A\bigl(V(\mathrm{modulus} \cdot \mathrm{param}^{-1})\bigr) = v_A(p)^{\mathrm{depth}(V)}$.
--
--   The principal-divisor law `hprinc`: for every nonzero $f \in F_M$ and every divisor $D$ with $D(V) = \mathrm{ord}_V f$ for all $V$, if every $V$ in the support of $D$ is of strict first type, or of strict second type, or else satisfies $\mathrm{red}_1 V = s.1$ for some $s \in SS$ and is fixed by inertia, then for every $s_0 \in SS$
--   $$\mathrm{proj}_e\Bigl(\mathrm{depthDual}(D) + \deg\bigl(\mathrm{sndDiv}(D)\bigr) \cdot \bigl(e(s_0)\,\mathrm{crossingCoord}(s_0)\bigr)\Bigr) = 0,$$
--   where `Psp.depthDual α hα SS depth D` is the sum over $s \in SS$ of `Psp.depthDiv α hα depth D s.1` times the crossing coordinate at $s$, `Psp.sndDiv` is the restriction of $D$ to the places of strict second type, `crossingCoord s` is the $s$-th coordinate functional on the character lattice of $SS$, and `componentGroupProj e` is the quotient map from $\mathrm{Hom}_{\mathbb{Z}}(\text{characterLattice } SS, \mathbb{Z})$ onto `componentGroup e`, the quotient by the image of `gramMap e`.
--
--   The representability hypothesis `hrep`: every element $x$ of `JHPlaceSpecialization.inertiaInvariants M H A`, the subgroup of $J_H(M)$ of classes fixed by every $\sigma \in$ `A.inertiaSubgroupIn ℚ`, is of the form $\mathrm{Pic}^0\text{-}\mathrm{class}(D)$ for some degree-zero divisor $D$ each place $V$ of whose support is fixed by inertia and is of strict first type, of strict second type, or satisfies $\mathrm{red}_1 V = s.1$ for some $s \in SS$.
--
--   Conclusion. Under these hypotheses there exists an additive group homomorphism
--   $$\mathrm{comp} \colon \mathrm{inertiaInvariants}\,M\,H\,A \longrightarrow \mathrm{componentGroup}\,e$$
--   satisfying `Psp.DepthCompLaw α (θ.toAlgHom.comp α) hα hβ δ SS e depth comp`, that is: for every degree-zero divisor $D$ on $F_M$ over $\overline{\mathbb{Q}}$ whose class lies in `inertiaInvariants M H A`, such that every place $V$ in the support of $D$ is fixed by the inertia subgroup acting through `arithmeticGalois` and is of strict first type, of strict second type, or satisfies $\mathrm{red}_1 V = s.1$ for some $s \in SS$, and for every $s_0 \in SS$,
--   $$\mathrm{comp}\bigl([D]\bigr) = \mathrm{componentGroupProj}_e\Bigl(\mathrm{Psp.depthDual}\,\alpha\,h\alpha\,SS\,\mathrm{depth}\,D + \deg\bigl(\mathrm{Psp.sndDiv}\,\alpha\,\beta\,h\alpha\,h\beta\,\delta\,D\bigr) \cdot \bigl(e(s_0)\,\mathrm{crossingCoord}(s_0)\bigr)\Bigr).$$
--   In particular the right-hand side is independent of the admissible representative $D$ of the class and of the chosen node $s_0$.
--
--   This is the construction step for the component map of the Néron model of $J_H(M)$ at a prime $p$ exactly dividing $M$, in the style of Raynaud's description of component groups of Jacobians of semistable curves: the value on an inertia-invariant divisor class is read off from the depths of its supporting places on the node annuli, corrected by the degree of its strict-second-type part times a vertex functional. It provides the homomorphism `comp` used in the assembly of the depth package for $J_H(M)$ at $p$, the $\Gamma_H$-level counterpart of the corresponding construction at level $\Gamma_0(Nq)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHPlaceSpecialization_exists_comp_depthCompLaw_of_principalLaw_of_annulusInf.lean

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_ComponentGroup
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_ModularCurve_JHNodeDepth
import Definitions.Def_ModularCurve_JHNodeDepthInf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JHNeronObjectAtP
open scoped MatrixGroups

open Classical in
open Classical in

theorem ModularCurve.JHPlaceSpecialization.exists_comp_depthCompLaw_of_principalLaw_of_annulusInf
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : (θ.toAlgHom.comp α).IsIntegral)
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v)
    (SS : Finset (Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))))
    (hSS : ∀ s, s ∈ SS ↔ s ∈ ssNodePairsQExp (ResidueField ↥A) (ΓN p M H hpM) p)
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)

    (hFix : ∀ y ∈ ssPlacesQExp (ResidueField ↥A) (ΓN p M H hpM) p,
      JHPlaceSpecialization.Fixed p M H hpM A δ y ∧
        JHPlaceSpecialization.Fixed p M H hpM A δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p y))
    (hTD : Psp.TypeDichotomy α (θ.toAlgHom.comp α) hα hβ δ)
    (hmodel : Rpd.IsModel α (θ.toAlgHom.comp α) hα hβ δ) (hO : Rpd.OrderLawFixed α (θ.toAlgHom.comp α) hα hβ δ)
    (hreg : Rpd.RegularityLaw α (θ.toAlgHom.comp α) hα hβ δ SS) (hnv : Rpd.NodeValueLaw α (θ.toAlgHom.comp α) hα hβ δ SS)

    (hθgal : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (f : ↥(xHFunctionFieldBar M H)),
      θ (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • f) =
        arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • θ f)

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

    (depth : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) → ℕ)
    (hdepth : ∀ (s : ↥SS) (An : AlgebraicCurve.Annulus A ↥(xHFunctionFieldBar M H)),
      ((∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
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
                (-(s.1.1.ord (Rpd.R₁.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A))) →
      Psp.AnnulusDepthLawInf α hα (s : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) An depth)

    (hprinc : ∀ (f : ↥(xHFunctionFieldBar M H)), f ≠ 0 → ∀ D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), (∀ V, D V = V.ord f) →
      (∀ V ∈ D.support,
        Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ V ∨ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ V ∨
          ((∃ s ∈ SS, Psp.reduceFst α hα V = s.1) ∧ (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.inertiaSubgroupIn ℚ →
            (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • V = V))) →
      ∀ s₀ : ↥SS,
        componentGroupProj e
          (Psp.depthDual α hα SS depth D +
            Divisor.degree (Psp.sndDiv α (θ.toAlgHom.comp α) hα hβ δ D) • ((e s₀ : ℤ) • crossingCoord s₀)) = 0)

    (hrep : ∀ x : ↥(JHPlaceSpecialization.inertiaInvariants M H A),
      ∃ D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H))),
        (∀ V ∈ (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)).support,
          (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.inertiaSubgroupIn ℚ →
            (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • V = V) ∧
          (Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ V ∨ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ V ∨ ∃ s ∈ SS, Psp.reduceFst α hα V = s.1)) ∧
        Pic0.mk D = (x : JH M H)) :
    ∃ comp : ↥(JHPlaceSpecialization.inertiaInvariants M H A) →+ componentGroup e,
      Psp.DepthCompLaw α (θ.toAlgHom.comp α) hα hβ δ SS e depth comp := by sorry
