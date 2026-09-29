-- Prove2me | Theorems.Thm_ModularCurve_JHPlaceSpecialization_exists_inertiaFixed_isStrict_add_isGoodDiv_gluedMk_eq_zero_add_principal_of_isTwistType_of_inertiaStable_of_annulus_of_fixRead
-- name    : ModularCurve.JHPlaceSpecialization.exists_inertiaFixed_isStrict_add_isGoodDiv_gluedMk_eq_zero_add_principal_of_isTwistType_of_inertiaStable_of_annulus_of_fixRead
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/029ecad9-2676-5282-aefd-90783029aada
-- title:
--   Twist-type divisors: inertia-fixed strict part plus glued-trivial good part
-- statement:
--   Throughout, $p$ is a prime and $M$ an integer with $p \mid M$ (`hpM`) and $p^2 \nmid M$ (`hpM2`), and $H \le (\mathbb{Z}/M)^{\times}$ is a subgroup containing every unit whose image under `ZMod.unitsMap` for $M/p \mid M$ is $1$ (`hHp`). Further, $A$ is a valuation subring of $\overline{\mathbb{Q}}$ lying over $p$ in the sense of `LiesOverPrime`, i.e. $p$ is a non-unit of $A$ (`hA`), and its residue field $\kappa =$ `ResidueField ↥A` is algebraically closed of characteristic $p$. Write $F_M$ for `xHFunctionFieldBar M H` (the base change to $\overline{\mathbb{Q}}$ of the Laurent-series function field `xHFunctionField M H`), $F_{M/p}$ for `xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)`, where `infSubgroup` is the image of $H$ in $(\mathbb{Z}/(M/p))^{\times}$, and $\bar F$ for `Fbar p M H hpM κ`, the $q$-expansion function field `qExpFunctionFieldC κ (ΓN p M H hpM)` in characteristic $p$. Places are [`AlgebraicCurve.Place`](def/AlgebraicCurve_DivisorClassGroup.html#L22)es, divisors are finitely supported $\mathbb{Z}$-valued functions on places, `Divisor.degZero` is the group of divisors of degree zero, and `Divisor.principal` is the group of divisors of the form $V \mapsto \operatorname{ord}_V f$ for a nonzero $f$.
--
--   The degeneracy data consist of: an automorphism $\theta$ of $F_M$ over $\overline{\mathbb{Q}}$; an algebra map $\alpha : F_{M/p} \to F_M$ over $\overline{\mathbb{Q}}$, integral (`hα`), such that $\beta := \theta \circ \alpha$ (written `θ.toAlgHom.comp α`) is integral (`hβ`); the hypothesis `hα_coe`, that $\alpha$ is the identity on underlying Laurent series; the hypothesis `hβ_coe`, that $\beta$ acts on underlying Laurent series by `qExpand` at $p$, i.e. by $q \mapsto q^{p}$; and `hθgal`, that $\theta$ commutes with the semilinear action `arithmeticGalois` of $\operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ on $F_M$. The diamond data consist of a unit $pb$ of $\mathbb{Z}/(M/p)$ whose underlying residue is $p$ (`hpb`) and a self-map $\delta$ of the set of places of $\bar F$ over $\kappa$, which by `hδ` is the action on places of the semilinear automorphism attached by `SemilinearAut.ofAlgAut` to `diamondActionModL κ (M/p) (infSubgroup p M H hpM)` evaluated at the lift [`CuspForm.gammaLift (M/p) pb`](def/CuspForm_HeckeOperatorFormsGammaH.html#L36) of $pb$ to $\Gamma_0(M/p)$. Finally $SS$ is a finite set of pairs of places of $\bar F$, which by `hSS` consists exactly of the supersingular node pairs `ssNodePairsQExp κ (ΓN p M H hpM) p`, that is, pairs $s$ with $s.2$ a supersingular place and $s.1 = \Phi(s.2)$, where $\Phi$ denotes `qExpFrobeniusPlaceModL`, the restriction of places along the $p$-power $q$-expansion map.
--
--   The specialisation data are a `JHPlaceSpecialization` $P_{sp}$ for $(p, M, H, hpM, A)$ — a map `sp` from places of $F_{M/p}$ to places of $\bar F$ together with a homomorphism on degree-zero Picard groups and the compatibility axioms of that structure (surjectivity, compatibility of push-forward of principal divisors with coefficientwise reduction of $q$-expansions, invariance under the inertia subgroup of $A$ over $\mathbb{Q}$, and transformation into $\Phi$ under a Frobenius element) — and a `ProlongationDatum` $R_{pd}$ for $P_{sp}$ and $\theta$, consisting of two regular prolongations $R_1, R_2$ of $A$ to $F_M$ with residues in $\bar F$, such that the residue of $R_1$ computes coefficientwise reduction of Laurent series, and $R_2$ is the $\theta$-pullback of $R_1$ ($f \in R_2$-integers iff $\theta f \in R_1$-integers, with equal residues). For a place $W$ of $F_M$ one writes $r_1(W) = P_{sp}.\mathrm{sp}(W|_{\alpha})$ and $r_2(W) = \delta\bigl(P_{sp}.\mathrm{sp}(W|_{\beta})\bigr)$ (`reduceFst`, `reduceSnd`); a place $v$ of $\bar F$ is *fixed* when $\Phi(\delta(\Phi v)) = v$, and *affine* (`IsAffinePlace`) when $v$ takes a finite value at the element of $\bar F$ whose $q$-expansion is `jqModC`. The place $W$ is *strict of the first kind* when $\delta(\Phi(r_1 W)) = r_2 W$ and $r_1 W$ is not fixed, and *strict of the second kind* when $r_1 W = \Phi(r_2 W)$ and $r_2 W$ is not fixed; a divisor is *good* (`IsGoodDiv`) when every place of its support is strict of one of the two kinds.
--
--   The hypotheses are grouped as follows, and none is omitted. *Combinatorial laws:* `hFix` asserts that every supersingular place $y$ and its image $\Phi(y)$ are fixed; `hTD` (`TypeDichotomy`) asserts that every place $W$ of $F_M$ satisfies $r_1 W = \Phi(r_2 W)$ or $\delta(\Phi(r_1 W)) = r_2 W$. *Model and numerical laws for $R_{pd}$:* `hmodel` is `IsModel`, the conjunction of the four clauses `DivisorLawFst`, `DivisorLawSnd`, `CuspLawInfty`, `CuspLawZero`; `hO` is `OrderLawFixed`, which for $f$ lying in both sets of integers with both residues nonzero, $D$ the divisor of $f$, and $v$ fixed and affine, equates $(r_1)_*D$ at $v$ with $\operatorname{ord}_v$ of the $R_1$-residue plus $\operatorname{ord}_{\delta(\Phi v)}$ of the $R_2$-residue; `hreg` is `RegularityLaw` for $SS$, whose two clauses give, for such $f$, non-negativity of the residue orders at fixed affine $v$ when $\operatorname{ord}_V f \ge 0$ for all $V$ with $r_1 V = v$, and existence of a common value of the two residues at the two components of each $s \in SS$ under the corresponding positivity assumption; `hnv` is `NodeValueLaw` for $SS$, which produces a nonzero common value $c \in \kappa$ of the two residues at $s.1$ and $s.2$ whenever no place $V$ with $\operatorname{ord}_V f \neq 0$ reduces to $(s.1, s.2)$. *Finiteness:* `hFixFin` asserts that the set of fixed places of $\bar F$ is finite. *Collision bounds:* `hLFst` and `hLSnd` assert, for the first and second kind respectively, that if $Q \neq Q'$ are strict places with the same reduction, that reduction being affine, if $n$ is a natural number nonzero in $\kappa$, if $g$ lies in the relevant integers with nonzero residue, $\operatorname{ord}_Q g = -n$, $\operatorname{ord}_{Q'} g = n$ and $\operatorname{ord}_W g = 0$ for every other strict place $W$ with the same reduction, and if $g = 1 + e\varepsilon$ with $e \in A$ and $\varepsilon$ in the same integers with nonzero residue, then the order of that residue of $\varepsilon$ at the reduction of $Q$ is at least $-1$. *Units:* `hUnit` asserts the existence of $u_1, u_2 \in F_M$ and divisors $D_1, D_2$ equal to the divisors of $u_1, u_2$ such that $u_1$ and $u_1^{-1}$ lie in the $R_1$-integers with nonzero residue of $u_1$, the push-forward along $r_1$ of the strict-first part of $D_1$ agrees at every non-fixed place $v$ with $\operatorname{ord}_v$ of that residue, and the push-forward along $r_1$ of the part of $D_1$ supported on infinity-side places agrees at $r_1 C$ with $\operatorname{ord}_{r_1 C}$ of that residue for every infinity-side $C$; that every nonzero $f$ admits $m \neq 0$ and $j \in \mathbb{Z}$ with $f^m u_1^{j}$ in the $R_2$-integers with nonzero residue; and the mirror-image statements for $u_2$, $R_2$, $r_2$, the strict-second part of $D_2$ and the zero-side places, together with the exchange condition producing $f^m u_2^{j}$ in the $R_1$-integers with nonzero residue. Here `IsInftySide C` means that $C$ is cuspidal and takes the value of a unit congruent to $1$ at $x'/x^{p}$, where $x, x'$ have $q$-expansions `jqModC` and `qExpand p jqModC`, and `IsZeroSide C` is the corresponding condition for $x/x'^{p}$ with `IsCuspidal'`. *Cusps and orientation:* `hcusp` asserts that every non-affine place of $\bar F$ is $r_1$ of some infinity-side place and $r_2$ of some zero-side place; `horientInf` asserts $\delta(\Phi(r_1 C)) = r_2 C$ for infinity-side $C$, and `horient0` asserts $r_1 C = \Phi(r_2 C)$ for zero-side $C$.
--
--   *Annulus data:* a function $e : SS \to \mathbb{N}$ with $e(s) > 0$ (`he`); the hypothesis `hAnn` and the explicitly given family $An : SS \to$ `Annulus A F_M` with `hAn`, both requiring of the annulus at $s$ the same seven clauses: its domain is the set of places $W$ with $r_1 W = s.1$ that are strict of neither kind; its modulus is $p^{e(s)}$ times a unit of $A$; its parameter is invariant under the action of the inertia subgroup `A.inertiaSubgroupIn ℚ` through `arithmeticGalois`; $(\text{modulus})^{-1}\cdot\text{param}$ lies in the $R_1$-integers; the parameter lies in the $R_2$-integers with nonzero residue; the $R_2$-residue of the parameter has order $1$ at $s.2$, and for every $f$ in the $R_2$-integers with nonzero residue and $\operatorname{ord}_P f = 0$ on the domain, the product of $P$-values $P(f)\cdot P(\text{param})^{-\operatorname{ord}_{s.2}(\text{residue of } f)}$ is a unit of $A$ at every $P$ of the domain; and the mirror clause for $\text{modulus}\cdot\text{param}^{-1}$ in the $R_1$-integers, with order $1$ at $s.1$ and the analogous unit reading. *Vertical slope:* `hVSlope` asserts that for every family of annuli satisfying exactly these clauses and every $k \in \mathbb{N}$ divisible by all $e(s)$, there are a nonzero $f \in F_M$ and $c \in \overline{\mathbb{Q}}$ with $c \cdot f$ in the $R_1$-integers with nonzero residue, such that the divisor of $f$ is good, $\operatorname{ord}_V f = 0$ for every $V$ whose reduction $r_1 V$ is fixed and distinct from all $s.1$, the $R_1$-residue of $c\cdot f$ has order $0$ at every fixed place distinct from all $s.1$, and for each $s$ there is $a \neq 0$ with $\operatorname{ord}_P f = 0$ and $P(f)\, a\, P(\text{param of } An\,s)^{-(k/e(s))}$ a unit of $A$ for all $P$ in the domain of $An\,s$. *Reading laws:* `hFixReadFst` and `hFixReadSnd` assert that for $g$ in the $R_1$- resp. $R_2$-integers with nonzero residue, and $v$ fixed and distinct from all $s.1$ resp. all $s.2$, vanishing of $\operatorname{ord}_V g$ for all $V$ with $r_1 V = v$ resp. $r_2 V = v$ forces $\operatorname{ord}_v$ of the residue to vanish; `hFixRegFst` and `hFixRegSnd` are the corresponding statements with non-negativity in place of vanishing, under the additional assumption that $v$ is affine. *Positions:* a function $pos : SS \to \{\text{places of } F_M\} \to \mathbb{Q}$ satisfying `AnnulusPositionLaw SS e An pos` (`hpos`), i.e. for $V$ in the domain of $An\,s$ one has $0 < pos\,s\,V < e(s)$ and the valuation of $V(\text{modulus}\cdot\text{param}^{-1})$ raised to the denominator of $pos\,s\,V$ equals the valuation of $p$ raised to the numerator; invariance of $pos$ under the inertia action on places (`hposσ`); and `hposD`, that for every integer $d$ with $0 < d < e(s)$ some inertia-fixed place of the domain of $An\,s$ has position $d$.
--
--   *The divisor:* $X$ is an element of `Divisor.degZero` for $F_M$ over $\overline{\mathbb{Q}}$ which is stable under the inertia subgroup of $A$ over $\mathbb{Q}$ (`hXst`), whose support consists of places that are strict of the first kind, strict of the second kind, or satisfy $r_1 V = s.1$ for some $s \in SS$ (`hXsupp`), and which is of twist type for the annulus data: `hXtw` states `IsTwistType`, namely that the predicate `IsTwistOf` holds for $X$ relative to $SS$, $e$, $An$, $pos$ and some twisting vector `a : TwistVec ↥SS`.
--
--   Under these hypotheses there exist degree-zero divisors $D_t$ and $D_2$ on $F_M$ over $\overline{\mathbb{Q}}$ such that:
--
--   1. every place $V$ in the support of $D_t$ is fixed by the action of every element of `A.inertiaSubgroupIn ℚ` through `arithmeticGalois`, and is strict of the first or of the second kind;
--
--   2. $D_2$ is good, that is, every place of its support is strict of the first or of the second kind;
--
--   3. the gluing datum of $D_2$, namely the triple consisting of the push-forward along $r_1$ of the strict-first part of $D_2$, the push-forward along $r_2$ of the strict-second part of $D_2$, and the zero family of constants, is admissible for $SS$ (both divisor components have degree zero, and the first vanishes at $s.1$ and the second at $s.2$ for every $s \in SS$), and its class `GluedPic0.mk` in the glued degree-zero Picard group of $SS$ is zero;
--
--   4. $X - D_t - D_2$ lies in `Divisor.principal`, i.e. it is the divisor of a nonzero element of $F_M$.
--
--   This is the decomposition ("kernel reach") step in the analysis of the degree-zero Picard group of the semistable reduction at $p$ of the modular curve $X_H(M)$ with $p \parallel M$: an inertia-stable admissible divisor class of twist type is represented by an inertia-fixed divisor supported on strict places plus a good divisor whose glued class on the special fibre vanishes. It is used in constructing representatives with strict or nodal support for inertia-invariant classes and in expressing Picard classes through component-group data, both on the way to the level-lowering input of the Fermat argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHPlaceSpecialization_exists_inertiaFixed_isStrict_add_isGoodDiv_gluedMk_eq_zero_add_principal_of_isTwistType_of_inertiaStable_of_annulus_of_fixRead.lean

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_ComponentGroup
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_ModularCurve_JHNodeDepth
import Definitions.Def_ModularCurve_JHNodeDepthInf
import Definitions.Def_ModularCurve_JHTwistType

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JHNeronObjectAtP
open scoped MatrixGroups

open Classical in

theorem ModularCurve.JHPlaceSpecialization.exists_inertiaFixed_isStrict_add_isGoodDiv_gluedMk_eq_zero_add_principal_of_isTwistType_of_inertiaStable_of_annulus_of_fixRead
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
        0 ≤ v.ord (Rpd.R₂.residue ⟨g, hg⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))

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
    (hposD : ∀ (s : ↥SS) (d : ℕ), 0 < d → d < e s → ∃ V ∈ (An s).dom,
      (∀ σ ∈ A.inertiaSubgroupIn ℚ, (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • V = V) ∧ pos s V = d)
    (X : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H))))
    (hXst : ∀ σ ∈ A.inertiaSubgroupIn ℚ, (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) = X)
    (hXsupp : ∀ V ∈ (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)).support,
      (Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ V ∨ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ V ∨ ∃ s ∈ SS, Psp.reduceFst α hα V = s.1))
    (hXtw : Psp.IsTwistType α (θ.toAlgHom.comp α) hα hβ δ SS e An pos (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))) :
    ∃ (Dt D₂ : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)))),
      (∀ V ∈ (Dt : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)).support,
        (∀ σ ∈ A.inertiaSubgroupIn ℚ, (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • V = V) ∧
        (Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ V ∨ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ V)) ∧
      Psp.IsGoodDiv α (θ.toAlgHom.comp α) hα hβ δ (D₂ : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) ∧
      (∃ hadm : Psp.glueData α (θ.toAlgHom.comp α) hα hβ δ SS (D₂ : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) ∈ GluingData.admissible SS,
        GluedPic0.mk SS ⟨Psp.glueData α (θ.toAlgHom.comp α) hα hβ δ SS (D₂ : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), hadm⟩ = 0) ∧
      ((X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) - Dt - D₂) ∈ Divisor.principal (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)) := by sorry
