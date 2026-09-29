-- Prove2me | Theorems.Thm_ModularCurve_JHPlaceSpecialization_exists_comp_sndDegLaw_surjective_repOfKer_principalGood_of_isModel_of_coe_of_unit_of_cusp_of_attachedAnnulus_of_slope_of_fixReg
-- name    : ModularCurve.JHPlaceSpecialization.exists_comp_sndDegLaw_surjective_repOfKer_principalGood_of_isModel_of_coe_of_unit_of_cusp_of_attachedAnnulus_of_slope_of_fixReg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/49048247-93e9-5174-9f07-0686fd08f9dc
-- title:
--   Surjective component map, good representatives, principal good divisor
-- statement:
--   Throughout, $p$ is a prime and $M$ a positive integer with $p \mid M$ (`hpM`) and $p^2 \nmid M$ (`hpM2`); $H \le (\mathbb{Z}/M)^\times$ is a subgroup containing every unit that becomes $1$ in $(\mathbb{Z}/(M/p))^\times$ (`hHp`), and $M/p$ is nonzero. Further, $A$ is a valuation subring of $\overline{\mathbb{Q}}$ lying over $p$ in the sense that $p$ is a non-unit of $A$ (`hA`), whose residue field $\kappa = \mathrm{ResidueField}\,A$ has characteristic $p$ and is algebraically closed. Write $F_M =$ `xHFunctionFieldBar M H` for the base change to $\overline{\mathbb{Q}}$ of the $q$-expansion function field of $X_H(M)$, $F_{M/p} =$ `xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)` for the corresponding field at level $(M/p, H')$ with $H'$ the image of $H$ in $(\mathbb{Z}/(M/p))^\times$, and $\bar F =$ `Fbar p M H hpM κ` for the $q$-expansion function field over $\kappa$ at level `ΓN p M H hpM`.
--
--   The data are: a $\overline{\mathbb{Q}}$-algebra automorphism $\theta$ of $F_M$; a $\overline{\mathbb{Q}}$-algebra map $\alpha : F_{M/p} \to F_M$ which is integral (`hα`) and acts as the identity on Laurent series (`hα_coe`), with $\beta := \theta \circ \alpha$ also integral (`hβ`) and acting on Laurent series by $q \mapsto q^p$, i.e. through `qExpand _ p` (`hβ_coe`); a unit $pb$ of $\mathbb{Z}/(M/p)$ whose underlying residue is $p$ (`hpb`); and a map $\delta$ on places of $\bar F$ over $\kappa$ which (`hδ`) is the action of the semilinear automorphism attached to the reduced diamond operator `diamondActionModL κ (M/p) (infSubgroup p M H hpM)` evaluated at the chosen $\Gamma_0(M/p)$-lift of $pb$. A finite set $SS$ of pairs of places of $\bar F$ is specified by `hSS` to consist exactly of the pairs $s$ with $s_2$ a supersingular place (in the sense of `ssPlacesQExp`) and $s_1 = \mathrm{Frob}(s_2)$, where $\mathrm{Frob} =$ `qExpFrobeniusPlaceModL κ (ΓN p M H hpM) p`. Finally, $Psp$ is a `JHPlaceSpecialization p M H hpM A`, that is, a surjective specialisation map $\mathrm{sp}$ from places of $F_{M/p}$ to places of $\bar F$ together with a homomorphism on degree-zero divisor classes and its axioms (compatibility with $q$-expansions and coefficientwise reduction, pushforward of principal divisors, invariance under the inertia subgroup, and conversion of a Frobenius element at $p$ into $\mathrm{Frob}$); and $Rpd$ is a `ProlongationDatum Psp θ`, consisting of two regular prolongations $R_1, R_2$ of $A$ to $F_M$ with residue maps onto $\bar F$, such that Laurent series with coefficients in $A$ lie in $R_1$ with coefficientwise reduction as residue, and $R_2$ is the pullback of $R_1$ along $\theta$ (both on integers and on residues).
--
--   Notation for the derived notions: $\mathrm{red}_1(W) = \mathrm{sp}(W|_\alpha)$ and $\mathrm{red}_2(W) = \delta(\mathrm{sp}(W|_\beta))$ for a place $W$ of $F_M$; a place $v$ of $\bar F$ is *$\delta$-fixed* when $\mathrm{Frob}(\delta(\mathrm{Frob}\,v)) = v$; $W$ is *strictly first* when $\delta(\mathrm{Frob}(\mathrm{red}_1 W)) = \mathrm{red}_2 W$ and $\mathrm{red}_1 W$ is not $\delta$-fixed, and *strictly second* when $\mathrm{red}_1 W = \mathrm{Frob}(\mathrm{red}_2 W)$ and $\mathrm{red}_2 W$ is not $\delta$-fixed; a divisor is *good* (`IsGoodDiv`) when every place of its support is strictly first or strictly second, and $\mathrm{fstDiv}$, $\mathrm{sndDiv}$ denote the restrictions of a divisor to the strictly first, resp. strictly second, places. A place $v$ of $\bar F$ is *affine* when the element of $\bar F$ with $q$-expansion $j(q)$ has a value at $v$; a place $C$ of $F_M$ is on the *infinity side* when it is cuspidal and $x'/x^p$ has at $C$ a value in $A$ with residue $1$, where $x, x'$ have $q$-expansions $j(q)$ and $j(q^p)$, and on the *zero side* when it is cuspidal in the sense of `IsCuspidal'` and $x/x'^p$ has such a value at $C$.
--
--   The hypotheses fall into the following groups. Supersingular fixing: `hFix` states that every supersingular place and its Frobenius image are $\delta$-fixed. Law block: `hTD` is the type dichotomy ($\mathrm{red}_1 W = \mathrm{Frob}(\mathrm{red}_2 W)$ or $\delta(\mathrm{Frob}(\mathrm{red}_1 W)) = \mathrm{red}_2 W$ for every place $W$ of $F_M$); `hmodel` is `Rpd.IsModel`, the conjunction of the two divisor laws and the two cusp laws for $\alpha, \beta, \delta$; `hO` is the fixed-place order law, computing the $\mathrm{red}_1$-pushforward of a principal divisor at a $\delta$-fixed affine place as the sum of the orders of the two residues; `hreg` is the regularity law at $\delta$-fixed affine places and at the pairs of $SS$; `hnv` is the node-value law at the pairs of $SS$. Equivariance: `hθgal` states that $\theta$ commutes with the arithmetic Galois action of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ on $F_M$. Finiteness: `hFixFin` states that the set of $\delta$-fixed places of $\bar F$ is finite.
--
--   Two symmetric local hypotheses `hLFst`, `hLSnd` bound pole orders of residues: for two distinct places $Q \neq Q'$ of $F_M$, both strictly first (resp. strictly second) with the same reduction $\mathrm{red}_1$ (resp. $\mathrm{red}_2$), that common reduction being affine, for every natural $n$ nonzero in $\kappa$, every $g \in R_1$ (resp. $R_2$) with nonzero residue satisfying $\mathrm{ord}_Q g = -n$, $\mathrm{ord}_{Q'} g = n$ and $\mathrm{ord}_W g = 0$ at every other place $W$ of the same strictness over the same reduction, and every $e \in A$, $\varepsilon \in R_1$ (resp. $R_2$) with nonzero residue such that $g = 1 + e\varepsilon$, one has $-1 \le \mathrm{ord}$ of the residue of $\varepsilon$ at that reduction.
--
--   The hypothesis `hUnit` asserts the existence of $u_1, u_2 \in F_M$ with divisors $D_1, D_2$ (so $D_i(W) = \mathrm{ord}_W u_i$ for all $W$) such that: $u_1$ and $u_1^{-1}$ lie in $R_1$ with $\mathrm{res}_1 u_1 \neq 0$, the $\mathrm{red}_1$-pushforward of $\mathrm{fstDiv}\,D_1$ agrees with $\mathrm{ord}(\mathrm{res}_1 u_1)$ at every place of $\bar F$ that is not $\delta$-fixed, and the $\mathrm{red}_1$-pushforward of the infinity-side part of $D_1$ agrees with $\mathrm{ord}(\mathrm{res}_1 u_1)$ at $\mathrm{red}_1 C$ for every infinity-side place $C$; every nonzero $f \in F_M$ admits $m \neq 0$ and $j \in \mathbb{Z}$ with $f^m u_1^{\,j} \in R_2$ of nonzero residue; and the mirror statements for $u_2$, $\mathrm{sndDiv}$, the zero side, $\mathrm{red}_2$ and $R_2$, together with: every nonzero $f$ admits $m \neq 0$ and $j$ with $f^m u_2^{\,j} \in R_1$ of nonzero residue.
--
--   Cusp covering `hcusp`: every non-affine place $w$ of $\bar F$ is $\mathrm{red}_1 C$ for some infinity-side place $C$ and $\mathrm{red}_2 C'$ for some zero-side place $C'$. Orientation `horientInf`, `horient0`: $\delta(\mathrm{Frob}(\mathrm{red}_1 C)) = \mathrm{red}_2 C$ for infinity-side $C$, and $\mathrm{red}_1 C = \mathrm{Frob}(\mathrm{red}_2 C)$ for zero-side $C$.
--
--   A width function $e : SS \to \mathbb{N}$ is given with $e(s) > 0$ for all $s$ (`he`). The attached-annulus hypothesis `hAnn` provides, for each $s \in SS$, an annulus $An$ over $A$ in $F_M$ (a set of places, a parameter and a modulus in the maximal ideal of $A$, with the annulus axioms) such that: its domain consists exactly of the places $W$ with $\mathrm{red}_1 W = s_1$ that are neither strictly first nor strictly second; its modulus is $p^{e(s)}$ times a unit of $A$; its parameter is fixed by the arithmetic Galois action of the inertia subgroup of $A$ in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$; $(\text{modulus})^{-1}\cdot \mathrm{param} \in R_1$; $\mathrm{param} \in R_2$ with nonzero residue; $\mathrm{ord}_{s_2}(\mathrm{res}_2\,\mathrm{param}) = 1$ and, for every $f \in R_2$ with nonzero residue having order $0$ at all places of the domain, $P(f)\cdot P(\mathrm{param})^{-\mathrm{ord}_{s_2}(\mathrm{res}_2 f)}$ is a unit of $A$ for every $P$ in the domain; and the mirror clauses on the first side for $(\text{modulus})\cdot \mathrm{param}^{-1} \in R_1$, with $\mathrm{ord}_{s_1}$ and $R_1$.
--
--   The slope hypothesis `hVSlope` asserts that for every family of annuli $An : SS \to \mathrm{Annulus}$ satisfying, for each $s$, the same list of clauses as in `hAnn`, and every $k \in \mathbb{N}$ divisible by all $e(s)$, there exist $f \in F_M$ and $c \in \overline{\mathbb{Q}}$ with $c \cdot f \in R_1$, $f \neq 0$, $\mathrm{res}_1(c\cdot f) \neq 0$, such that the divisor of $f$ is good; $\mathrm{ord}_V f = 0$ at every place $V$ of $F_M$ with $\mathrm{red}_1 V$ $\delta$-fixed and distinct from all $s_1$; $\mathrm{ord}_v(\mathrm{res}_1(c\cdot f)) = 0$ at every $\delta$-fixed place $v$ distinct from all $s_1$; and for each $s$ there is $a \neq 0$ in $\overline{\mathbb{Q}}$ with $\mathrm{ord}_P f = 0$ and $P(f)\cdot a \cdot P((An\,s).\mathrm{param})^{-(k/e(s))}$ a unit of $A$ for all $P$ in $(An\,s).\mathrm{dom}$.
--
--   Finally, two reading hypotheses `hFixReadFst`, `hFixReadSnd` state that a function $g \in R_i$ with nonzero residue whose order vanishes at every place of $F_M$ reducing to a $\delta$-fixed place $v$ distinct from all $s_1$ (resp. all $s_2$) has $\mathrm{ord}_v(\mathrm{res}_i g) = 0$; and two regularity hypotheses `hFixRegFst`, `hFixRegSnd` state the corresponding one-sided inequality: if such a $v$ is moreover affine and $g \in R_i$ has nonzero residue and non-negative order at every place reducing to $v$, then $0 \le \mathrm{ord}_v(\mathrm{res}_i g)$.
--
--   Under these hypotheses there exists an additive homomorphism $\mathrm{comp}$ from the inertia invariants `JHPlaceSpecialization.inertiaInvariants M H A` of $J_H(M) = \mathrm{Pic}^0(F_M)$ — the subgroup of classes fixed by every element of the inertia subgroup of $A$ in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ — to the component group `componentGroup e`, i.e. the $\mathbb{Z}$-dual of the character lattice $\ker(\deg) \subseteq (SS \to \mathbb{Z})$ modulo the image of `gramMap e`, with the following four properties.
--
--   First, for every degree-zero divisor $D$ on $F_M$ whose class $[D]$ lies in the inertia invariants, if $D$ is good then for every $s_0 \in SS$
--   $$\mathrm{comp}\,[D] = \deg(\mathrm{sndDiv}\,D)\cdot \mathrm{componentGroupProj}\,e\bigl( e(s_0)\cdot (\mathrm{pr}_{s_0}\circ \iota)\bigr),$$
--   where $\iota$ is the inclusion of the character lattice into $SS \to \mathbb{Z}$ and $\mathrm{pr}_{s_0}$ the $s_0$-th coordinate projection.
--
--   Second, $\mathrm{comp}$ is surjective.
--
--   Third, every $x$ in the inertia invariants with $\mathrm{comp}\,x = 0$ is represented by a good divisor: there is a degree-zero divisor $D$ on $F_M$ which is good and satisfies $[D] = x$ in $J_H(M)$.
--
--   Fourth, there exists a divisor $G$ on $F_M$ which is principal (the divisor of a nonzero element of $F_M$), is good, and has bidegree
--   $$\deg(\mathrm{fstDiv}\,G) = \sum_{s \in SS} \frac{\mathrm{lcm}_{s'}\,e(s')}{e(s)}, \qquad \deg(\mathrm{sndDiv}\,G) = -\sum_{s \in SS} \frac{\mathrm{lcm}_{s'}\,e(s')}{e(s)} .$$
--
--   This is the component-group step in the analysis of the Jacobian $J_H(M)$ at a prime $p$ with $p \parallel M$, where the special fibre is a union of two copies of the level-$(M/p)$ curve glued at supersingular points with widths $e$: it produces a surjective homomorphism from the inertia invariants of $J_H(M)$ onto the combinatorial component group $\Phi(e)$, computes it on good degree-zero divisors through the degree of the second-side part, represents its kernel classes by good divisors, and exhibits a principal good divisor of bidegree $(m(e), -m(e))$. It is invoked by [`ModularCurve.JHPlaceSpecialization.exists_componentMap_gluedSpecialization_of_isModel_of_coe_of_unit_of_cusp_of_attachedAnnulus_of_slope_of_fixReg`](thm.html#ModularCurve.JHPlaceSpecialization.exists_componentMap_gluedSpecialization_of_isModel_of_coe_of_unit_of_cusp_of_attachedAnnulus_of_slope_of_fixReg), and the resulting description of the component group feeds the level-lowering part of the argument. The statement is obtained from [`ModularCurve.JHPlaceSpecialization.exists_depth_comp_depthCompLaw_annulusDepthLaw_sndDegLaw_surjective_repOfKer_principalGood_of_coe_of_unit_of_cusp_of_attachedAnnulus_of_slope_of_fixReg`](thm.html#ModularCurve.JHPlaceSpecialization.exists_depth_comp_depthCompLaw_annulusDepthLaw_sndDegLaw_surjective_repOfKer_principalGood_of_coe_of_unit_of_cusp_of_attachedAnnulus_of_slope_of_fixReg) by discarding the depth data and the depth and annulus laws provided there.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHPlaceSpecialization_exists_comp_sndDegLaw_surjective_repOfKer_principalGood_of_isModel_of_coe_of_unit_of_cusp_of_attachedAnnulus_of_slope_of_fixReg.lean

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_ComponentGroup
import Definitions.Def_AlgebraicCurve_SemistableCharts

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve.JHNeronObjectAtP
open ModularCurve
open scoped MatrixGroups

open Classical in

theorem ModularCurve.JHPlaceSpecialization.exists_comp_sndDegLaw_surjective_repOfKer_principalGood_of_isModel_of_coe_of_unit_of_cusp_of_attachedAnnulus_of_slope_of_fixReg
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
    (hβ_coe : ∀ u, (((θ.toAlgHom.comp α) u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))

    (hFixFin : {v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) | JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v}.Finite)

    (hLFst : ∀ (Q Q' : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ Q → Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ Q' →
      Psp.reduceFst α hα Q' = Psp.reduceFst α hα Q → Q' ≠ Q → JHPlaceSpecialization.IsAffinePlace p M H hpM A (Psp.reduceFst α hα Q) →
      ∀ (n : ℕ), (n : (ResidueField ↥A)) ≠ 0 → ∀ (g : ↥(xHFunctionFieldBar M H)) (hg₁ : g ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨g, hg₁⟩ ≠ 0 →
      Q.ord g = -(n : ℤ) → Q'.ord g = n →
      (∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W → Psp.reduceFst α hα W = Psp.reduceFst α hα Q → W ≠ Q → W ≠ Q' → W.ord g = 0) →
      ∀ (e : ↥A) (ε : ↥(xHFunctionFieldBar M H)) (hε₁ : ε ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨ε, hε₁⟩ ≠ 0 →
      g = 1 + algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (e : AlgebraicClosure ℚ) * ε →
      -1 ≤ (Psp.reduceFst α hα Q).ord (Rpd.R₁.residue ⟨ε, hε₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (hLSnd : ∀ (Q Q' : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ Q → Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ Q' →
      Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Q' = Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Q → Q' ≠ Q → JHPlaceSpecialization.IsAffinePlace p M H hpM A (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Q) →
      ∀ (n : ℕ), (n : (ResidueField ↥A)) ≠ 0 → ∀ (g : ↥(xHFunctionFieldBar M H)) (hg₂ : g ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨g, hg₂⟩ ≠ 0 →
      Q.ord g = -(n : ℤ) → Q'.ord g = n →
      (∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ W → Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ W = Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Q → W ≠ Q → W ≠ Q' → W.ord g = 0) →
      ∀ (e : ↥A) (ε : ↥(xHFunctionFieldBar M H)) (hε₂ : ε ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨ε, hε₂⟩ ≠ 0 →
      g = 1 + algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (e : AlgebraicClosure ℚ) * ε →
      -1 ≤ (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Q).ord (Rpd.R₂.residue ⟨ε, hε₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))

    (hUnit : ∃ (u₁ u₂ : ↥(xHFunctionFieldBar M H)) (D₁ D₂ : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)),
      (∀ W, D₁ W = W.ord u₁) ∧ (∀ W, D₂ W = W.ord u₂) ∧

      (∃ h₁ : u₁ ∈ Rpd.R₁.integers, Rpd.R₁.residue ⟨u₁, h₁⟩ ≠ 0 ∧ u₁⁻¹ ∈ Rpd.R₁.integers ∧
        (∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), ¬ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v →
          Finsupp.mapDomain (Psp.reduceFst α hα) (Psp.fstDiv α (θ.toAlgHom.comp α) hα hβ δ D₁) v = v.ord (Rpd.R₁.residue ⟨u₁, h₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))) ∧
        (∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A) C →
          Finsupp.mapDomain (Psp.reduceFst α hα) (D₁.filter (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A))) (Psp.reduceFst α hα C) =
            (Psp.reduceFst α hα C).ord (Rpd.R₁.residue ⟨u₁, h₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))) ∧
      (∀ f : ↥(xHFunctionFieldBar M H), f ≠ 0 → ∃ (m : ℕ) (j : ℤ), m ≠ 0 ∧
        ∃ h₂ : f ^ m * u₁ ^ j ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨f ^ m * u₁ ^ j, h₂⟩ ≠ 0) ∧

      (∃ h₂ : u₂ ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨u₂, h₂⟩ ≠ 0 ∧ u₂⁻¹ ∈ Rpd.R₂.integers ∧
        (∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), ¬ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v →
          Finsupp.mapDomain (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ) (Psp.sndDiv α (θ.toAlgHom.comp α) hα hβ δ D₂) v = v.ord (Rpd.R₂.residue ⟨u₂, h₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))) ∧
        (∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A) C →
          Finsupp.mapDomain (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ) (D₂.filter (JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A))) (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ C) =
            (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ C).ord (Rpd.R₂.residue ⟨u₂, h₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))) ∧
      (∀ f : ↥(xHFunctionFieldBar M H), f ≠ 0 → ∃ (m : ℕ) (j : ℤ), m ≠ 0 ∧
        ∃ h₁ : f ^ m * u₂ ^ j ∈ Rpd.R₁.integers, Rpd.R₁.residue ⟨f ^ m * u₂ ^ j, h₁⟩ ≠ 0))
    (hcusp : ∀ w : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)),
      ¬ (JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A)) w →
        (∃ C, (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A)) C ∧ Psp.reduceFst α hα C = w) ∧
        (∃ C, (JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A)) C ∧ Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ C = w))

    (horientInf : ∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A) C →
      δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (Psp.reduceFst α hα C)) = Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ C)
    (horient0 : ∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A) C →
      Psp.reduceFst α hα C = qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ C))

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

    (hVSlope : ∀ An : ↥SS → AlgebraicCurve.Annulus A ↥(xHFunctionFieldBar M H),
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
          (∀ v : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)), JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v → (∀ s ∈ SS, v ≠ s.1) →
            v.ord (Rpd.R₁.residue ⟨c • f, hc⟩ : Fbar p M H hpM (ResidueField ↥A)) = 0) ∧
          (∀ s : ↥SS, ∃ a : AlgebraicClosure ℚ, a ≠ 0 ∧ ∀ P ∈ (An s).dom, P.ord f = 0 ∧
            ∃ h : P.evalAt f * a * (P.evalAt (An s).param) ^ (-((k / e s : ℕ) : ℤ)) ∈ A, IsUnit (⟨_, h⟩ : ↥A)))

    (hFixReadFst : ∀ (g : ↥(xHFunctionFieldBar M H)) (hg : g ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨g, hg⟩ ≠ 0 →
      ∀ v : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)), JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v → (∀ s ∈ SS, v ≠ s.1) →
        (∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.reduceFst α hα V = v → V.ord g = 0) →
        v.ord (Rpd.R₁.residue ⟨g, hg⟩ : Fbar p M H hpM (ResidueField ↥A)) = 0)
    (hFixReadSnd : ∀ (g : ↥(xHFunctionFieldBar M H)) (hg : g ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨g, hg⟩ ≠ 0 →
      ∀ v : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)), JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v → (∀ s ∈ SS, v ≠ s.2) →
        (∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ V = v → V.ord g = 0) →
        v.ord (Rpd.R₂.residue ⟨g, hg⟩ : Fbar p M H hpM (ResidueField ↥A)) = 0)

    (hFixRegFst : ∀ (g : ↥(xHFunctionFieldBar M H)) (hg : g ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨g, hg⟩ ≠ 0 →
      ∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v → JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A) v → (∀ s ∈ SS, v ≠ s.1) →
        (∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.reduceFst α hα V = v → 0 ≤ V.ord g) →
        0 ≤ v.ord (Rpd.R₁.residue ⟨g, hg⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hFixRegSnd : ∀ (g : ↥(xHFunctionFieldBar M H)) (hg : g ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨g, hg⟩ ≠ 0 →
      ∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v → JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A) v → (∀ s ∈ SS, v ≠ s.2) →
        (∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ V = v → 0 ≤ V.ord g) →
        0 ≤ v.ord (Rpd.R₂.residue ⟨g, hg⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) :
    ∃ (comp : ↥(JHPlaceSpecialization.inertiaInvariants M H A) →+ componentGroup e),

      (∀ (D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H))))
          (hI : Pic0.mk D ∈ JHPlaceSpecialization.inertiaInvariants M H A),
          Psp.IsGoodDiv α (θ.toAlgHom.comp α) hα hβ δ (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) →
          ∀ s₀ : ↥SS,
            comp ⟨Pic0.mk D, hI⟩ =
              (Psp.sndDiv α (θ.toAlgHom.comp α) hα hβ δ (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))).degree •
                componentGroupProj e
                  ((e s₀ : ℤ) • (LinearMap.proj s₀ : (↥SS → ℤ) →ₗ[ℤ] ℤ).comp (characterLattice ↥SS).subtype)) ∧
      Function.Surjective comp ∧

      (∀ x : ↥(JHPlaceSpecialization.inertiaInvariants M H A), comp x = 0 →
        ∃ D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H))),
          Psp.IsGoodDiv α (θ.toAlgHom.comp α) hα hβ δ (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) ∧ Pic0.mk D = (x : JH M H)) ∧

      (∃ G : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
        Divisor.IsPrincipal G ∧ Psp.IsGoodDiv α (θ.toAlgHom.comp α) hα hβ δ G ∧
          (Psp.fstDiv α (θ.toAlgHom.comp α) hα hβ δ G).degree = ((∑ s : ↥SS, Finset.univ.lcm e / e s : ℕ) : ℤ) ∧
          (Psp.sndDiv α (θ.toAlgHom.comp α) hα hβ δ G).degree = -((∑ s : ↥SS, Finset.univ.lcm e / e s : ℕ) : ℤ)) := by sorry
