-- Prove2me | Theorems.Thm_ModularCurve_JHPlaceSpecialization_den_twistPosMoment_eq_one_of_inertiaStable_of_annulus
-- name    : ModularCurve.JHPlaceSpecialization.den_twistPosMoment_eq_one_of_inertiaStable_of_annulus
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/e9322521-11a2-513f-8e54-7ec09e10e178
-- title:
--   Integrality of annulus position moments of inertia-stable divisors
-- statement:
--   Throughout, $p$ is a prime and $M$ a nonzero natural number with $p \mid M$ and $p^2 \nmid M$; $H$ is a subgroup of $(\mathbb Z/M)^\times$ subject to the hypothesis `hHp`, that every unit $u$ of $\mathbb Z/M$ whose image under the reduction map $(\mathbb Z/M)^\times \to (\mathbb Z/(M/p))^\times$ is $1$ belongs to $H$, and $M/p$ is nonzero. Further, $A$ is a valuation subring of $\overline{\mathbb Q}$ for which $p$ is a nonunit (`A.LiesOverPrime p`), and its residue field $\kappa$ is of characteristic $p$ and algebraically closed. Write $F_M$ for `xHFunctionFieldBar M H`, the base change to $\overline{\mathbb Q}$ of the intermediate field `xHFunctionField M H` of Laurent series over $\mathbb Q$; $F_{M/p}$ for the analogous field at level $M/p$ for the subgroup `infSubgroup p M H hpM`, the image of $H$ in $(\mathbb Z/(M/p))^\times$; and $\bar F$ for `Fbar p M H hpM κ`, the $q$-expansion function field over $\kappa$ at level `ΓN p M H hpM`. A place of a field over its base field is, as in [`AlgebraicCurve.Place`](def/AlgebraicCurve_DivisorClassGroup.html#L22), a proper valuation subring containing the base field and having principal ideals, with the associated order function `ord`, value predicate `HasValue` and residual evaluation `evalAt`; `qExpFrobeniusPlaceModL κ Γ p` denotes restriction of a place along the characteristic-$p$ Frobenius endomorphism of the $q$-expansion function field.
--
--   The function-field data consist of: an automorphism $\theta$ of $F_M$ over $\overline{\mathbb Q}$; an algebra map $\alpha : F_{M/p} \to F_M$ over $\overline{\mathbb Q}$, integral by `hα`, such that $\alpha$ followed by $\theta$ is integral by `hβ`; the normalisation hypotheses `hα_coe`, that $\alpha$ is the identity on Laurent series (the Laurent expansion of $\alpha u$ equals that of $u$), and `hβ_coe`, that the Laurent expansion of $(\theta \circ \alpha)(u)$ is obtained from that of $u$ by the substitution `qExpand` of parameter $p$ (that is, $q \mapsto q^p$); and `hθgal`, that $\theta$ commutes with the semilinear action `arithmeticGalois` of $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ on $F_M$.
--
--   The diamond datum consists of a unit $\mathrm{pb}$ of $\mathbb Z/(M/p)$ whose underlying element is $p$ (`hpb`), and a self-map $\delta$ of the set of places of $\bar F$ over $\kappa$ which, by `hδ`, acts as the semilinear automorphism attached by `SemilinearAut.ofAlgAut` to the diamond automorphism `diamondActionModL κ (M/p) (infSubgroup p M H hpM)` evaluated at the $\Gamma_0(M/p)$-lift [`CuspForm.gammaLift (M/p) pb`](def/CuspForm_HeckeOperatorFormsGammaH.html#L36) of $\mathrm{pb}$. For a place $v$ of $\bar F$, the predicate `Fixed δ v` says that applying Frobenius, then $\delta$, then Frobenius returns $v$; `IsAffinePlace v` says that $v$ takes a value in $\kappa$ at an element of $\bar F$ whose $q$-expansion is `jqModC κ`.
--
--   The node set is a finite set $SS$ of pairs of places of $\bar F$ which, by `hSS`, is exactly `ssNodePairsQExp κ (ΓN p M H hpM) p`: the pairs $s$ with $s.2$ a supersingular place and $s.1$ its Frobenius image.
--
--   The specialisation data are `Psp : JHPlaceSpecialization p M H hpM A`, consisting of a surjective map `sp` from places of $F_{M/p}$ to places of $\bar F$ together with a homomorphism on degree-zero divisor classes, compatible with reduction of $q$-expansions and with divisors of functions, invariant under the inertia subgroup of $A$ over $\mathbb Q$ and equivariant for Frobenius elements at $p$; and `Rpd : Psp.ProlongationDatum θ`, a pair of regular prolongations $R_1, R_2$ of $A$ to $F_M$ with residue field $\bar F$ (valuation subrings `integers` with surjective residue maps whose kernels are the maximal ideals and which are compatible with $A$), related by $f \in R_2.\mathrm{integers} \iff \theta f \in R_1.\mathrm{integers}$ and by the matching of residues through $\theta$. For a place $W$ of $F_M$, $\mathrm{red}_1 W = \mathrm{sp}(W|_\alpha)$ and $\mathrm{red}_2 W = \delta(\mathrm{sp}(W|_{\theta\circ\alpha}))$ denote `Psp.reduceFst` and `Psp.reduceSnd`; $W$ is of strict first type when $\delta(\mathrm{Frob}(\mathrm{red}_1 W)) = \mathrm{red}_2 W$ and $\mathrm{red}_1 W$ is not `Fixed`, and of strict second type when $\mathrm{red}_1 W = \mathrm{Frob}(\mathrm{red}_2 W)$ and $\mathrm{red}_2 W$ is not `Fixed`; `fstDiv` and `sndDiv` are the restrictions of a divisor to the places of strict first, respectively strict second, type.
--
--   The structural laws assumed are: `hFix`, that for every supersingular place $y$ in `ssPlacesQExp κ (ΓN p M H hpM) p` both $y$ and its Frobenius image are `Fixed` for $\delta$; `hTD`, the type dichotomy, that every place $W$ of $F_M$ satisfies $\mathrm{red}_1 W = \mathrm{Frob}(\mathrm{red}_2 W)$ or $\delta(\mathrm{Frob}(\mathrm{red}_1 W)) = \mathrm{red}_2 W$; `hmodel`, that `Rpd` is a model, i.e. the conjunction of the four laws `DivisorLawFst`, `DivisorLawSnd`, `CuspLawInfty` and `CuspLawZero`; `hO`, the order law at fixed places, that for $f$ lying in both rings of integers with nonzero residues and with divisor $D$, and for every `Fixed` affine place $v$, the pushforward of $D$ along $\mathrm{red}_1$ at $v$ equals $\mathrm{ord}_v$ of the $R_1$-residue of $f$ plus $\mathrm{ord}$ of the $R_2$-residue of $f$ at $\delta(\mathrm{Frob}\,v)$; `hreg`, the regularity law for $SS$ (two clauses: nonnegativity of the orders of the two residues at `Fixed` affine places, and the existence of common residual values at the two components of a node, whenever $f$ has nonnegative orders at all places above); `hnv`, the node value law for $SS$ (the two residues take one and the same nonzero value at $s.1$ and $s.2$ whenever no place with $\mathrm{ord}\,f \neq 0$ reduces to the pair $s$); and `hFixFin`, that the set of $\delta$-`Fixed` places of $\bar F$ is finite.
--
--   The two local hypotheses `hLFst` and `hLSnd` are mirror-image statements for the first and second types. `hLFst` asserts: for all places $Q, Q'$ of $F_M$ of strict first type with $\mathrm{red}_1 Q' = \mathrm{red}_1 Q$ and $Q' \neq Q$, this common reduction being an affine place, for every natural number $n$ whose image in $\kappa$ is nonzero, every $g \in R_1.\mathrm{integers}$ with nonzero $R_1$-residue satisfying $\mathrm{ord}_Q g = -n$, $\mathrm{ord}_{Q'} g = n$ and $\mathrm{ord}_W g = 0$ for every further place $W$ of strict first type with the same reduction, and for every $e \in A$ and every $\varepsilon \in R_1.\mathrm{integers}$ with nonzero $R_1$-residue such that $g = 1 + e\,\varepsilon$, the order of the $R_1$-residue of $\varepsilon$ at $\mathrm{red}_1 Q$ is at least $-1$. `hLSnd` is the same statement with the second type, $\mathrm{red}_2$ and $R_2$ in place of the first type, $\mathrm{red}_1$ and $R_1$.
--
--   The hypothesis `hUnit` posits elements $u_1, u_2$ of $F_M$ and divisors $D_1, D_2$ which are the divisors of $u_1$ and of $u_2$, such that: $u_1$ and $u_1^{-1}$ lie in $R_1.\mathrm{integers}$ with nonzero residue for $u_1$, the pushforward along $\mathrm{red}_1$ of the strict-first-type part of $D_1$ agrees at every non-`Fixed` place $v$ with $\mathrm{ord}_v$ of the $R_1$-residue of $u_1$, and the pushforward along $\mathrm{red}_1$ of the part of $D_1$ supported on places on the $\infty$-side agrees with that order at $\mathrm{red}_1 C$ for every $\infty$-side place $C$; every nonzero $f$ admits $m \neq 0$ and $j \in \mathbb Z$ with $f^m u_1^{\,j} \in R_2.\mathrm{integers}$ of nonzero residue; and symmetrically for $u_2$, with $R_2$, $\mathrm{red}_2$, the strict-second-type part of $D_2$, the zero-side places, and $f^m u_2^{\,j} \in R_1.\mathrm{integers}$ of nonzero residue. Here a place $C$ of $F_M$ is on the $\infty$-side when it is cuspidal and takes the value of a unit residue $\tau \in A$ (with residue $1$) at $x'/x^p$, where $x$ has $q$-expansion `jqModC` and $x'$ its $p$-th substitution; it is on the zero-side in the `IsCuspidal'` sense with $x/x'^p$ in place of $x'/x^p$. The hypothesis `hcusp` requires every non-affine place $w$ of $\bar F$ to be $\mathrm{red}_1$ of some $\infty$-side place and $\mathrm{red}_2$ of some zero-side place; the orientation hypotheses are `horientInf`, that $\delta(\mathrm{Frob}(\mathrm{red}_1 C)) = \mathrm{red}_2 C$ for every $\infty$-side place $C$, and `horient0`, that $\mathrm{red}_1 C = \mathrm{Frob}(\mathrm{red}_2 C)$ for every zero-side place $C$.
--
--   The annulus data are: a function $e : SS \to \mathbb N$ with $e(s) > 0$ for all $s$ (`he`); the hypothesis `hAnn`, asserting for each $s \in SS$ the existence of an annulus (in the sense of [`AlgebraicCurve.Annulus A F_M`](def/AlgebraicCurve_SemistableCharts.html#L86): a set `dom` of places, a parameter `param`, a modulus in the maximal ideal of $A$, with the rationality, value-attainment, uniqueness, order-one and unit-principle axioms of that structure) whose domain is the set of places $W$ with $\mathrm{red}_1 W = s.1$ that are of neither strict type, whose modulus is $p^{e(s)}$ times a unit of $A$, whose parameter is fixed by the `arithmeticGalois` action of the inertia subgroup `A.inertiaSubgroupIn ℚ`, for which $(\mathrm{modulus})^{-1}\cdot\mathrm{param} \in R_1.\mathrm{integers}$ and $\mathrm{param} \in R_2.\mathrm{integers}$ with nonzero residue, such that the $R_2$-residue of $\mathrm{param}$ has order $1$ at $s.2$ and, for every $f \in R_2.\mathrm{integers}$ with nonzero residue and with $\mathrm{ord}_P f = 0$ for all $P$ in the domain, the product of $P.\mathrm{evalAt}\,f$ with $(P.\mathrm{evalAt}\,\mathrm{param})$ raised to minus the order at $s.2$ of the $R_2$-residue of $f$ lies in $A$ and is a unit there, and symmetrically that $\mathrm{modulus}\cdot\mathrm{param}^{-1} \in R_1.\mathrm{integers}$ has $R_1$-residue of order $1$ at $s.1$ with the corresponding unit statement for $R_1$, $s.1$ and $\mathrm{modulus}\cdot\mathrm{param}^{-1}$; a chosen family $An : SS \to \mathrm{Annulus}\,A\,F_M$, for which `hAn` asserts exactly the same list of properties of $An(s)$ for each $s$; a function $\mathrm{pos} : SS \to \{\text{places of } F_M\} \to \mathbb Q$ satisfying the position law `hpos` (`AnnulusPositionLaw`), namely that for every $s$ and every $V$ in the domain of $An(s)$ one has $0 < \mathrm{pos}_s(V) < e(s)$ and the valuation of $V.\mathrm{evalAt}$ of $\mathrm{modulus}\cdot\mathrm{param}^{-1}$ raised to the denominator of $\mathrm{pos}_s(V)$ equals the valuation of $p$ raised to the numerator of $\mathrm{pos}_s(V)$; and `hposσ`, that each $\mathrm{pos}_s$ is invariant under the `arithmeticGalois` action of the inertia subgroup of $A$ over $\mathbb Q$.
--
--   Finally, $X$ is a divisor of degree zero on $F_M$ over $\overline{\mathbb Q}$ (an element of `Divisor.degZero`) which, by `hXst`, is fixed by the `arithmeticGalois` action of every element of `A.inertiaSubgroupIn ℚ`.
--
--   Under these hypotheses the conclusion is: for every $s \in SS$ the rational number
--   $$\mathrm{twistPosMoment}(s) \;=\; \sum_{V \in \mathrm{supp}\,X,\; V \in \mathrm{dom}\,An(s)} X(V)\,\mathrm{pos}_s(V)$$
--   has denominator $1$, that is, it is an integer.
--
--   This is the integrality statement for the position moments of an inertia-stable degree-zero divisor along the node annuli of the curve $X_H(M)$ at a prime $p$ exactly dividing $M$: it is the arithmetic input showing that the rational positions attached to the annuli of the semistable reduction combine to integral quantities on inertia-invariant divisors. It feeds the identification of the twist type in [`ModularCurve.JHPlaceSpecialization.isTwistType_of_componentGroupProj_depthDual_eq_zero_of_inertiaStable_of_annulus`](thm.html#ModularCurve.JHPlaceSpecialization.isTwistType_of_componentGroupProj_depthDual_eq_zero_of_inertiaStable_of_annulus), part of the analysis of the special fibre of the Jacobian used in the level-lowering step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHPlaceSpecialization_den_twistPosMoment_eq_one_of_inertiaStable_of_annulus.lean

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_ComponentGroup
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_ModularCurve_JHNodeDepth
import Definitions.Def_ModularCurve_JHNodeDepthInf
import Definitions.Def_ModularCurve_JHTwistType
import Definitions.Def_ModularCurve_JHTwistedDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JHNeronObjectAtP
open scoped MatrixGroups
open Classical in

theorem ModularCurve.JHPlaceSpecialization.den_twistPosMoment_eq_one_of_inertiaStable_of_annulus
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

    (An : ↥SS → AlgebraicCurve.Annulus A ↥(xHFunctionFieldBar M H))
    (hAn : ∀ s : ↥SS,
      (∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
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
              (-(s.1.1.ord (Rpd.R₁.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A)))
    (pos : ↥SS → Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) → ℚ)
    (hpos : JHPlaceSpecialization.AnnulusPositionLaw SS e An pos)
    (hposσ : ∀ (s : ↥SS), ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
      pos s ((arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • V) = pos s V)
    (X : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H))))
    (hXst : ∀ σ ∈ A.inertiaSubgroupIn ℚ, (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) = X) :
    ∀ (s : ↥SS), (JHPlaceSpecialization.twistPosMoment SS An pos (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) s).den = 1 := by sorry
