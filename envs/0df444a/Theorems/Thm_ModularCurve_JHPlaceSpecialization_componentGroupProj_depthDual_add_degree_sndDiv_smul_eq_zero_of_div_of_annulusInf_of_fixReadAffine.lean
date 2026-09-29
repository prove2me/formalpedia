-- Prove2me | Theorems.Thm_ModularCurve_JHPlaceSpecialization_componentGroupProj_depthDual_add_degree_sndDiv_smul_eq_zero_of_div_of_annulusInf_of_fixReadAffine
-- name    : ModularCurve.JHPlaceSpecialization.componentGroupProj_depthDual_add_degree_sndDiv_smul_eq_zero_of_div_of_annulusInf_of_fixReadAffine
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/f11d1b1f-093a-5a72-a42d-52bb7df3e2e7
-- title:
--   Vanishing depth component class of a principal divisor
-- statement:
--   Throughout, $p$ is a prime and $M$ a nonzero natural number with $p \mid M$ (`hpM`) and $p^2 \nmid M$ (`hpM2`), and $H \le (\mathbb{Z}/M)^\times$ is a subgroup containing every unit that becomes $1$ in $(\mathbb{Z}/(M/p))^\times$ (`hHp`). Further, $A$ is a valuation subring of $\overline{\mathbb{Q}}$ lying over $p$ in the sense that $p$ is a nonunit of $A$ (`hA`), with residue field $\kappa := \mathrm{ResidueField}(A)$ of characteristic $p$ and algebraically closed. Write $F := \,$`xHFunctionFieldBar M H` for the compositum of $\overline{\mathbb{Q}}$ with the function field of $X_H(M)$ inside $\overline{\mathbb{Q}}((q))$, $F' := \,$`xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)` for the corresponding field at level $M/p$ with the image subgroup `infSubgroup p M H hpM` $= H \cdot$ (image under reduction), and $\bar F := \,$`Fbar p M H hpM κ` $=\,$`qExpFunctionFieldC κ (ΓN p M H hpM)` for the characteristic-$p$ $q$-expansion function field of the relevant congruence subgroup.
--
--   The data are: an $\overline{\mathbb{Q}}$-algebra automorphism $\theta$ of $F$; an $\overline{\mathbb{Q}}$-algebra map $\alpha : F' \to F$, integral (`hα`), such that $\theta \circ \alpha$ is integral as well (`hβ`), with $\alpha$ acting as the identity on Laurent series (`hα_coe`) and $\theta \circ \alpha$ acting as the substitution $q \mapsto q^{p}$, i.e. as `qExpand`$_p$, on Laurent series (`hβ_coe`); a unit $pb$ of $\mathbb{Z}/(M/p)$ whose underlying residue is $p$ (`hpb`); a self-map $\delta$ of the set of $\kappa$-places of $\bar F$ which, by `hδ`, is the action on places of the semilinear automorphism attached to the diamond operator `diamondActionModL κ (M / p) (infSubgroup p M H hpM)` evaluated at a $\Gamma_0(M/p)$-lift of $pb$; a finite set $SS$ of pairs of $\kappa$-places of $\bar F$ which, by `hSS`, is exactly the set `ssNodePairsQExp κ (ΓN p M H hpM) p`, that is the set of pairs $s$ with $s.2$ supersingular and $s.1$ the $q$-expansion Frobenius place of $s.2$; a place specialisation $Psp$ of level $(p,M,H,A)$, i.e. a map $\mathrm{sp}$ from $\overline{\mathbb{Q}}$-places of $F'$ to $\kappa$-places of $\bar F$ together with a map on degree-zero divisor classes and the compatibilities recorded in `JHPlaceSpecialization` (surjectivity, reading of principal divisors through $q$-expansions, inertia-invariance, Frobenius-equivariance); and a prolongation datum $Rpd$ for $Psp$ and $\theta$, consisting of two regular prolongations $R_1, R_2$ of $A$-integers of $F$ with residues in $\bar F$, compatible with $q$-expansions and linked by $\theta$.
--
--   For a place $W$ of $F$, $\,$`Psp.reduceFst α hα W` $= \mathrm{sp}(W|_{\alpha})$ and `Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ W` $= \delta(\mathrm{sp}(W|_{\theta\alpha}))$; $W$ is strict of the first kind when $\delta(\mathrm{Frob}(\mathrm{reduceFst}\,W)) = \mathrm{reduceSnd}\,W$ and $\mathrm{reduceFst}\,W$ is not $\delta$-fixed, and strict of the second kind when $\mathrm{reduceFst}\,W = \mathrm{Frob}(\mathrm{reduceSnd}\,W)$ and $\mathrm{reduceSnd}\,W$ is not $\delta$-fixed, where $\mathrm{Frob} = \,$`qExpFrobeniusPlaceModL` and a place $v$ is $\delta$-fixed (`Fixed`) when $\mathrm{Frob}(\delta(\mathrm{Frob}(v))) = v$; `fstDiv` and `sndDiv` are the restrictions of a divisor to the strict places of the respective kind. A place $v$ of $\bar F$ is affine (`IsAffinePlace`) when the element of $\bar F$ with $q$-expansion $j$ has a finite value at $v$; a place $C$ of $F$ is on the $\infty$-side (resp. $0$-side) when it is cuspidal in the corresponding sense and, for elements $x,x'$ of $F$ with $q$-expansions $j(q)$ and $j(q^p)$, the function $x'/x^p$ (resp. $x/x'^p$) has at $C$ a value in $A$ with residue $1$.
--
--   The hypotheses are grouped as follows, each group summarised here where indicated. Geometric position of the supersingular places: `hFix` states that every place in `ssPlacesQExp κ (ΓN p M H hpM) p` and its Frobenius image are $\delta$-fixed, and `hFixFin` that the set of $\delta$-fixed places of $\bar F$ is finite. Structural laws for the prolongation datum: `hTD` (type dichotomy: every place of $F$ satisfies $\mathrm{reduceFst} = \mathrm{Frob}\circ\mathrm{reduceSnd}$ or $\delta\circ\mathrm{Frob}\circ\mathrm{reduceFst} = \mathrm{reduceSnd}$), `hmodel` (the model law: the two divisor laws and the two cusp laws), `hO` (the order law at $\delta$-fixed affine places: for $f$ a unit for both $R_1$ and $R_2$, the $\mathrm{reduceFst}$-pushforward of $\operatorname{div} f$ at such a place $v$ is $\mathrm{ord}_v(\mathrm{res}_1 f) + \mathrm{ord}_{\delta(\mathrm{Frob}\,v)}(\mathrm{res}_2 f)$), `hreg` (the regularity law at $\delta$-fixed affine places and at the pairs in $SS$) and `hnv` (the node value law: the two residues take a common nonzero value at the two members of a pair of $SS$ not met by the divisor). Galois compatibility: `hθgal` states that $\theta$ commutes with the arithmetic Galois action of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ on $F$.
--
--   Two local-bound groups, `hLFst` and `hLSnd`, are imposed symmetrically for the first and second kind: if $Q \ne Q'$ are distinct strict places of that kind with the same reduction, this reduction being affine, if $n$ is a natural number nonzero in $\kappa$, if $g$ is an integer for the corresponding prolongation with nonzero residue, $\mathrm{ord}_Q g = -n$, $\mathrm{ord}_{Q'} g = n$ and $\mathrm{ord}_W g = 0$ for all further strict places $W$ of that kind with the same reduction, and if $g = 1 + e\,\varepsilon$ with $e \in A$ and $\varepsilon$ an integer for that prolongation with nonzero residue, then the order of the residue of $\varepsilon$ at the common reduction of $Q$ is at least $-1$.
--
--   The group `hUnit` asserts the existence of $u_1, u_2 \in F$ and divisors $D_1, D_2$ equal to $\operatorname{div} u_1$, $\operatorname{div} u_2$ such that: $u_1$ and $u_1^{-1}$ are $R_1$-integral with nonzero $R_1$-residue, the $\mathrm{reduceFst}$-pushforward of `fstDiv` $D_1$ reads the order of that residue at every non-$\delta$-fixed place, and the $\mathrm{reduceFst}$-pushforward of the $\infty$-side part of $D_1$ reads it at the reduction of every $\infty$-side place; every nonzero $f \in F$ admits $m \ne 0$ and $j \in \mathbb{Z}$ with $f^m u_1^{j}$ an $R_2$-integer of nonzero residue; and symmetrically for $u_2$ with $R_2$, $\mathrm{reduceSnd}$, `sndDiv`, the $0$-side, and $f^m u_2^{j}$ an $R_1$-integer of nonzero residue. The group `hcusp` states that every non-affine place of $\bar F$ is the $\mathrm{reduceFst}$-image of an $\infty$-side place and the $\mathrm{reduceSnd}$-image of a $0$-side place; `horientInf` and `horient0` state that $\delta(\mathrm{Frob}(\mathrm{reduceFst}\,C)) = \mathrm{reduceSnd}\,C$ for $C$ on the $\infty$-side and $\mathrm{reduceFst}\,C = \mathrm{Frob}(\mathrm{reduceSnd}\,C)$ for $C$ on the $0$-side.
--
--   The widths are a function $e : SS \to \mathbb{N}$ with $e(s) > 0$ for all $s$ (`he`). The group `hAnn` provides, for each $s \in SS$, an annulus $An$ over $A$ in $F$ (in the sense of [`AlgebraicCurve.Annulus`](def/AlgebraicCurve_SemistableCharts.html#L86)) whose domain consists exactly of the places $W$ with $\mathrm{reduceFst}\,W = s.1$ that are strict of neither kind, whose modulus is $p^{e(s)}$ times a unit of $A$, whose parameter is fixed by the arithmetic Galois action of the inertia subgroup of $A$ over $\mathbb{Q}$, and such that: $\mathrm{modulus}^{-1}\cdot\mathrm{param}$ is an $R_1$-integer; $\mathrm{param}$ is an $R_2$-integer with nonzero residue; the $R_2$-residue of $\mathrm{param}$ has order $1$ at $s.2$, and for every $R_2$-integer $f$ of nonzero residue with vanishing order on the whole annulus domain, at each $P$ of the domain the element $P(f)\cdot P(\mathrm{param})^{-\mathrm{ord}_{s.2}(\mathrm{res}_2 f)}$ lies in $A$ and is a unit there; and the mirror clauses for $\mathrm{modulus}\cdot\mathrm{param}^{-1}$ as an $R_1$-integer of order $1$ at $s.1$ with the analogous unit condition on slopes.
--
--   The groups `hFixReadFst` and `hFixReadSnd` state that an $R_1$- (resp. $R_2$-) integer $g$ of nonzero residue has residue of order $0$ at every $\delta$-fixed affine place $v$ that is distinct from all first (resp. second) components of pairs in $SS$, provided $\mathrm{ord}_V g = 0$ for every place $V$ of $F$ with $\mathrm{reduceFst}\,V = v$ (resp. $\mathrm{reduceSnd}\,V = v$). The four one-sided laws `hOSFst`, `hOSSnd`, `hOSInf`, `hOSZero` extend the corresponding clauses of `hUnit` to arbitrary units: for every $R_1$-integer $g$ with nonzero residue and every divisor $E = \operatorname{div} g$, the $\mathrm{reduceFst}$-pushforward of `fstDiv` $E$ at a non-$\delta$-fixed place $v$ equals $\mathrm{ord}_v(\mathrm{res}_1 g)$ (`hOSFst`), and the $\mathrm{reduceFst}$-pushforward of the $\infty$-side part of $E$ at the reduction of an $\infty$-side place $c$ equals the order of $\mathrm{res}_1 g$ there (`hOSInf`); `hOSSnd` and `hOSZero` are the statements obtained by replacing $R_1$, `fstDiv`, $\mathrm{reduceFst}$ and the $\infty$-side by $R_2$, `sndDiv`, $\mathrm{reduceSnd}$ and the $0$-side.
--
--   Finally, $\mathrm{depth}$ is a function from places of $F$ to $\mathbb{N}$ satisfying `hdepth`: for every $s \in SS$ and every annulus $An$ satisfying the full list of conditions of `hAnn` for $s$, the law `Psp.AnnulusDepthLawInf` holds, namely for every place $V$ of $F$ with $\mathrm{reduceFst}\,V = s.1$ that is fixed by the arithmetic Galois action of the inertia subgroup of $A$ over $\mathbb{Q}$, $$A\text{-}\mathrm{val}\bigl(V(\mathrm{modulus}\cdot\mathrm{param}^{-1})\bigr) = A\text{-}\mathrm{val}(p)^{\mathrm{depth}(V)}.$$ The remaining data are a nonzero $f \in F$, a divisor $D$ with $D(V) = \mathrm{ord}_V f$ for all $V$ (`hDf`), the support condition `hsupp` that every $V$ in the support of $D$ is strict of the first kind, or strict of the second kind, or else satisfies $\mathrm{reduceFst}\,V = s.1$ for some $s \in SS$ and is fixed by the arithmetic Galois action of the inertia subgroup, and an element $s_0 \in SS$.
--
--   The conclusion is that the projection `componentGroupProj e` — the quotient map from $\mathrm{Hom}_{\mathbb{Z}}(\mathrm{characterLattice}\, SS, \mathbb{Z})$ to the component group `componentGroup e`, i.e. the quotient by the range of the Gram map `gramMap e` — annihilates the element
--   $$\mathrm{depthDual} + \deg\bigl(\mathrm{sndDiv}(D)\bigr)\cdot\bigl(e(s_0)\cdot \mathrm{crossingCoord}(s_0)\bigr),$$
--   where $\mathrm{depthDual} = \,$`Psp.depthDual α hα SS depth D` $= \sum_{s \in SS} \bigl(\mathrm{depthDiv}(\mathrm{depth}, D, s.1)\bigr)\cdot \mathrm{crossingCoord}(s)$, $\mathrm{crossingCoord}(s)$ is the $s$-th coordinate functional on the character lattice of $SS$, and $\deg$ is the degree of the divisor `Psp.sndDiv α (θ.toAlgHom.comp α) hα hβ δ D`, the part of $D$ supported on the places strict of the second kind. Equivalently, that element lies in the image of `gramMap e`.
--
--   This is the principal-divisor half of Raynaud's description, via the minimal regular model, of the group of connected components of the Néron model of $J_H(M)$ at a prime $p$ exactly dividing $M$: at a supersingular node of width $e(s)$ the chain of $e(s)-1$ lines is read off by the depth of a place, and the resulting depth functional of a principal divisor is trivial in the component group. It is the $\Gamma_H$-level statement, in the annulus language, of the corresponding result at level $\Gamma_0(Nq)$, and it is used in the construction of the depth datum and the attendant component-group laws for $J_H(M)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHPlaceSpecialization_componentGroupProj_depthDual_add_degree_sndDiv_smul_eq_zero_of_div_of_annulusInf_of_fixReadAffine.lean

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

theorem ModularCurve.JHPlaceSpecialization.componentGroupProj_depthDual_add_degree_sndDiv_smul_eq_zero_of_div_of_annulusInf_of_fixReadAffine
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

    (hFixReadFst : ∀ (g : ↥(xHFunctionFieldBar M H)) (hg : g ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨g, hg⟩ ≠ 0 →
      ∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v → JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A) v → (∀ s ∈ SS, v ≠ s.1) →
        (∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.reduceFst α hα V = v → V.ord g = 0) →
        v.ord (Rpd.R₁.residue ⟨g, hg⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) = 0)
    (hFixReadSnd : ∀ (g : ↥(xHFunctionFieldBar M H)) (hg : g ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨g, hg⟩ ≠ 0 →
      ∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v → JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A) v → (∀ s ∈ SS, v ≠ s.2) →
        (∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ V = v → V.ord g = 0) →
        v.ord (Rpd.R₂.residue ⟨g, hg⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) = 0)

    (hOSFst : ∀ (g : ↥(xHFunctionFieldBar M H)) (h₁ : g ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨g, h₁⟩ ≠ 0 →
      ∀ E : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), (∀ W, E W = W.ord g) →
        ∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), ¬ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v →
          Finsupp.mapDomain (Psp.reduceFst α hα) (Psp.fstDiv α (θ.toAlgHom.comp α) hα hβ δ E) v = v.ord (Rpd.R₁.residue ⟨g, h₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (hOSSnd : ∀ (g : ↥(xHFunctionFieldBar M H)) (h₂ : g ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨g, h₂⟩ ≠ 0 →
      ∀ E : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), (∀ W, E W = W.ord g) →
        ∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), ¬ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v →
          Finsupp.mapDomain (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ) (Psp.sndDiv α (θ.toAlgHom.comp α) hα hβ δ E) v = v.ord (Rpd.R₂.residue ⟨g, h₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (hOSInf : ∀ (g : ↥(xHFunctionFieldBar M H)) (h₁ : g ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨g, h₁⟩ ≠ 0 →
      ∀ E : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), (∀ W, E W = W.ord g) →
        ∀ c : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A) c →
          Finsupp.mapDomain (Psp.reduceFst α hα) (E.filter (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A))) (Psp.reduceFst α hα c) =
            (Psp.reduceFst α hα c).ord (Rpd.R₁.residue ⟨g, h₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (hOSZero : ∀ (g : ↥(xHFunctionFieldBar M H)) (h₂ : g ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨g, h₂⟩ ≠ 0 →
      ∀ E : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), (∀ W, E W = W.ord g) →
        ∀ c : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A) c →
          Finsupp.mapDomain (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ) (E.filter (JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A))) (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ c) =
            (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ c).ord (Rpd.R₂.residue ⟨g, h₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
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
    (f : ↥(xHFunctionFieldBar M H)) (hf : f ≠ 0)
    (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (hDf : ∀ V, D V = V.ord f)
    (hsupp : ∀ V ∈ D.support,
      Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ V ∨ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ V ∨
        ((∃ s ∈ SS, Psp.reduceFst α hα V = s.1) ∧
          ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.inertiaSubgroupIn ℚ →
            (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • V = V))
    (s₀ : ↥SS) :
    componentGroupProj e
        (Psp.depthDual α hα SS depth D +
          Divisor.degree (Psp.sndDiv α (θ.toAlgHom.comp α) hα hβ δ D) • ((e s₀ : ℤ) • crossingCoord s₀)) = 0 := by sorry
