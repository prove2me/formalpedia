-- Prove2me | Theorems.Thm_ModularCurve_JHPlaceSpecialization_exists_principal_degZero_forall_support_sub_inertia_smul_eq_of_splitting
-- name    : ModularCurve.JHPlaceSpecialization.exists_principal_degZero_forall_support_sub_inertia_smul_eq_of_splitting
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/4ceabfcb-7b26-5235-ab04-fc29bec1e3c4
-- title:
--   Inertia-fixed admissible representative of an inertia-stable divisor
-- statement:
--   Throughout, $p$ is a prime and $M$ a natural number with $p \mid M$ (`hpM`) and $p^{2} \nmid M$ (`hpM2`), and $H$ is a subgroup of $(\mathbb Z/M)^{\times}$; the hypothesis `hHp` requires $H$ to contain every unit of $\mathbb Z/M$ whose image under the reduction map `ZMod.unitsMap` to $(\mathbb Z/(M/p))^{\times}$ is trivial. Further, $A$ is a valuation subring of $\overline{\mathbb Q}$ with `A.LiesOverPrime p`, that is, $p$ is a nonunit of $A$ (`hA`), and its residue field $\kappa =$ `ResidueField ↥A` is algebraically closed of characteristic $p$.
--
--   Three function fields occur. $FM$ denotes `xHFunctionFieldBar M H`, the base change to $\overline{\mathbb Q}$ of the $q$-expansion field `xHFunctionField M H` of $X_H(M)$ inside the Laurent series over $\mathbb Q$; $FMp$ denotes the same construction at level $M/p$ for the group `infSubgroup p M H hpM`, the image of $H$ in $(\mathbb Z/(M/p))^{\times}$; and $Fb$ denotes `Fbar p M H hpM κ`, the $q$-expansion function field over $\kappa$ of the group `ΓN p M H hpM`. Places, divisors, orders and degrees are those of `AlgebraicCurve`: a divisor is a finitely supported integer-valued function on places, `Divisor.degZero` is the kernel of the degree homomorphism, and `Divisor.principal` consists of the divisors of the form $v \mapsto \operatorname{ord}_v f$ for some $f \neq 0$. Write $\Phi$ for `qExpFrobeniusPlaceModL κ (ΓN p M H hpM) p`, the restriction of places along the $p$-power Frobenius of the $q$-expansion field, and let the inertia group `A.inertiaSubgroupIn ℚ` act on elements, places and divisors of $FM$ through the semilinear action `arithmeticGalois`.
--
--   The degeneracy data are: a $\overline{\mathbb Q}$-algebra automorphism $\theta$ of $FM$; an integral $\overline{\mathbb Q}$-algebra homomorphism $\alpha : FMp \to FM$ (`hα`) which is the identity on Laurent series (`hα_coe`); the composite $\beta = \theta \circ \alpha$, also integral (`hβ`), which on Laurent series is the substitution `qExpand` by $p$, i.e. $q \mapsto q^{p}$ (`hβ_coe`); and the hypothesis `hθgal` that $\theta$ commutes with the `arithmeticGalois` action of every $\sigma \in \operatorname{Gal}(\overline{\mathbb Q}/\mathbb Q)$ on $FM$. A unit `pb` of $\mathbb Z/(M/p)$ is given whose underlying residue is $p$ (`hpb`), and $\delta$ is a self-map of the places of $Fb$ over $\kappa$ which (`hδ`) is the pointwise action of the semilinear automorphism attached, via `SemilinearAut.ofAlgAut`, to the reduced diamond operator `diamondActionModL κ (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)`. The finset $SS$ of pairs of places of $Fb$ has, by `hSS`, exactly the supersingular node pairs `ssNodePairsQExp κ (ΓN p M H hpM) p` as members: pairs $s$ with $s.2$ a supersingular place and $s.1 = \Phi(s.2)$.
--
--   The reduction data are a `JHPlaceSpecialization p M H hpM A`, written `Psp`, consisting of a specialization map `sp` from places of $FMp$ to places of $Fb$ and a homomorphism `spPic0` on degree-zero classes, subject to the axioms of that structure (compatibility of `mapDomain sp` with divisors of functions and with reduction of $q$-expansions, surjectivity of `sp`, invariance under inertia, equivariance for Frobenius elements at $p$, and compatibility of `spPic0` with `mapDomain sp`); and a `ProlongationDatum Psp θ`, written `Rpd`, consisting of two regular prolongations `Rpd.R₁`, `Rpd.R₂` of $A$ from $FM$ to $Fb$, each with its subring `integers` and residue map `residue` into $Fb$, such that reductions of Laurent series with coefficients in $A$ lie in `R₁` with the expected residue, $f \in$ `R₂.integers` if and only if $\theta f \in$ `R₁.integers`, and the `R₂`-residue of $f$ is the `R₁`-residue of $\theta f$.
--
--   Derived notions used below: `Psp.reduceFst α hα W = sp(W|_{\alpha})` and `Psp.reduceSnd β hβ δ W = δ(sp(W|_{\beta}))`; a place $v$ of $Fb$ is $\delta$-fixed (`Fixed`) when $\Phi(\delta(\Phi v)) = v$, and affine (`IsAffinePlace`) when some element of $Fb$ with Laurent expansion `jqModC κ` has a value in $\kappa$ at $v$; a place $W$ of $FM$ is strict of the first kind (`IsStrictFst`) when $\delta(\Phi(\mathrm{reduceFst}\,W)) = \mathrm{reduceSnd}\,W$ and $\mathrm{reduceFst}\,W$ is not $\delta$-fixed, and strict of the second kind (`IsStrictSnd`) when $\mathrm{reduceFst}\,W = \Phi(\mathrm{reduceSnd}\,W)$ and $\mathrm{reduceSnd}\,W$ is not $\delta$-fixed. A place $V$ of $FM$ is called admissible here when it is strict of the first kind, or strict of the second kind, or $\mathrm{reduceFst}\,V = s.1$ for some $s \in SS$; it is called inertia-fixed when $\sigma \cdot V = V$ for every $\sigma \in$ `A.inertiaSubgroupIn ℚ`. Finally, `IsInftySide` (respectively `IsZeroSide`) says of a place $W$ of $FM$ that it is cuspidal in the sense of `IsCuspidal` (respectively `IsCuspidal'`) and that for elements $x, x'$ of $FM$ with Laurent expansions `jqModC` and `qExpand p (jqModC)` the function $x'/x^{p}$ (respectively $x/x'^{p}$) takes at $W$ the value of an element of $A$ with residue $1$.
--
--   The hypotheses on this data fall into the following groups.
--
--   Supersingular and dichotomy laws: `hFix` states that every place $y$ in `ssPlacesQExp κ (ΓN p M H hpM) p` and also $\Phi(y)$ are $\delta$-fixed; `hTD` (`TypeDichotomy`) states that every place $W$ of $FM$ satisfies $\mathrm{reduceFst}\,W = \Phi(\mathrm{reduceSnd}\,W)$ or $\delta(\Phi(\mathrm{reduceFst}\,W)) = \mathrm{reduceSnd}\,W$; `hFixFin` states that the set of $\delta$-fixed places of $Fb$ is finite.
--
--   Model and order laws for `Rpd`: `hmodel` is `IsModel`, the conjunction of the divisor laws `DivisorLawFst`, `DivisorLawSnd` and the cusp laws `CuspLawInfty`, `CuspLawZero`; `hO` (`OrderLawFixed`) states that for $f$ lying in both `integers` with both residues nonzero and $D$ the divisor of $f$, at every $\delta$-fixed affine place $v$ one has $(\mathrm{mapDomain}\ \mathrm{reduceFst}\ D)(v) = \operatorname{ord}_v(\mathrm{R₁.residue}\,f) + \operatorname{ord}_{\delta(\Phi v)}(\mathrm{R₂.residue}\,f)$; `hreg` (`RegularityLaw`, two clauses) asserts non-negativity of the orders of the two residues at $\delta$-fixed affine places, and the existence of a common value of the two residues at each $s \in SS$, whenever $f$ has non-negative orders at all places above the place in question; `hnv` (`NodeValueLaw`) asserts that for such $f$ and each $s \in SS$ over which $f$ has no zeros or poles, the two residues take one and the same nonzero value at $s.1$ and $s.2$.
--
--   Local order bounds `hLFst` and `hLSnd`: for places $Q \neq Q'$ both strict of the first kind (respectively of the second kind) with the same first (respectively second) reduction, that reduction being affine, for every natural number $n$ nonzero in $\kappa$ and every $g$ in `R₁.integers` (respectively `R₂.integers`) with nonzero residue such that $\operatorname{ord}_Q g = -n$, $\operatorname{ord}_{Q'} g = n$ and $\operatorname{ord}_W g = 0$ for all further strict places $W$ with the same reduction, and for all $e \in A$ and $\varepsilon$ in the same `integers` with nonzero residue satisfying $g = 1 + e\,\varepsilon$, the order of the residue of $\varepsilon$ at that reduction is at least $-1$.
--
--   Modular units `hUnit`: there exist $u_1, u_2 \in FM$ and divisors $D_1, D_2$ with $D_1(W) = \operatorname{ord}_W u_1$ and $D_2(W) = \operatorname{ord}_W u_2$ at every place $W$, such that $u_1$ and $u_1^{-1}$ lie in `R₁.integers` with the residue of $u_1$ nonzero, the push-forward under `reduceFst` of the strict-first part `fstDiv` of $D_1$ agrees at every non-$\delta$-fixed place $v$ with $\operatorname{ord}_v$ of the `R₁`-residue of $u_1$, and the push-forward under `reduceFst` of the restriction of $D_1$ to the infinity-side places agrees, at $\mathrm{reduceFst}\,C$ for every infinity-side $C$, with the order there of that residue; every nonzero $f \in FM$ admits $m \neq 0$ and $j \in \mathbb Z$ with $f^{m}u_1^{j} \in$ `R₂.integers` of nonzero residue; and the mirror-image clauses hold for $u_2$, with `R₂`, `reduceSnd`, `sndDiv`, the zero-side places, and $f^{m}u_2^{j} \in$ `R₁.integers` of nonzero residue.
--
--   Cusps: `hcusp` states that every non-affine place $w$ of $Fb$ is the first reduction of some infinity-side place and the second reduction of some zero-side place; `horientInf` states that $\delta(\Phi(\mathrm{reduceFst}\,C)) = \mathrm{reduceSnd}\,C$ for infinity-side $C$, and `horient0` that $\mathrm{reduceFst}\,C = \Phi(\mathrm{reduceSnd}\,C)$ for zero-side $C$.
--
--   Annuli: a function $e : SS \to \mathbb N$ with $e(s) > 0$ (`he`) is given, and `hAnn` (seven clauses, summarised here) provides for each $s \in SS$ an [`AlgebraicCurve.Annulus A FM`](def/AlgebraicCurve_SemistableCharts.html#L86), that is, a set `dom` of places, a parameter `param` in $FM$ and a modulus in the maximal ideal of $A$ subject to the axioms of that structure, such that: `dom` consists exactly of the places $W$ with $\mathrm{reduceFst}\,W = s.1.1$ that are strict of neither kind; the modulus is $p^{e(s)}$ times a unit of $A$; `param` is fixed by the `arithmeticGalois` action of the inertia group; $\mathrm{modulus}^{-1}\cdot\mathrm{param}$ lies in `R₁.integers`; `param` lies in `R₂.integers` with nonzero residue, the order at $s.1.2$ of its `R₂`-residue is $1$, and for every $f$ in `R₂.integers` of nonzero residue with vanishing orders on `dom`, the product of the value of $f$ at $P \in \mathrm{dom}$ with the value of `param` at $P$ raised to minus the order at $s.1.2$ of the residue of $f$ is a unit of $A$; and the corresponding clause for $\mathrm{modulus}\cdot\mathrm{param}^{-1}$ in `R₁.integers`, with order $1$ at $s.1.1$ and the analogous unit statement for `R₁`-residue orders.
--
--   Splitting of heads `hsplit`: for every degree-zero divisor $X$ of $FM$ that is fixed by the `arithmeticGalois` action of every $\sigma \in$ `A.inertiaSubgroupIn ℚ` and all of whose support points are admissible, there exist degree-zero divisors $D_1, D_2$ such that every support point of $D_1$ is inertia-fixed and admissible, $D_2$ is good (`IsGoodDiv`: each support point strict of the first or of the second kind), the glue data `Psp.glueData … SS D₂` is `admissible` and its class in `GluedPic0 SS` is zero, and $X - D_1 - D_2$ is principal.
--
--   Finally, $E$ is a divisor of $FM$ fixed by the inertia action (`hEst`) all of whose support points are admissible (`hEgood`).
--
--   Under these hypotheses there exists a divisor $C$ of $FM$ over $\overline{\mathbb Q}$ such that: $C$ is principal, i.e. $C(v) = \operatorname{ord}_v f$ at every place $v$ for some nonzero $f \in FM$; $C$ has degree zero; and every place $V$ in the support of $E - C$ is both fixed by the `arithmeticGalois` action of every $\sigma \in$ `A.inertiaSubgroupIn ℚ` and admissible, i.e. strict of the first kind, or strict of the second kind, or such that $\mathrm{reduceFst}\,V = s.1$ for some $s \in SS$.
--
--   This is the inertia-fixing step in the construction of divisor-class representatives on the semistable fibre at $p$ of $X_H(M)$ for $p \parallel M$: an inertia-stable divisor with support in the strict and nodal loci is moved, modulo a principal degree-zero divisor, onto a support consisting of inertia-fixed places of the same kind. It is used by [`ModularCurve.JHPlaceSpecialization.exists_rep_inertiaFixed_support_strict_or_node_of_mem_inertiaInvariants_of_annulus_of_fixReg`](thm.html#ModularCurve.JHPlaceSpecialization.exists_rep_inertiaFixed_support_strict_or_node_of_mem_inertiaInvariants_of_annulus_of_fixReg), which produces such representatives for classes in the inertia invariants of the Picard group.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHPlaceSpecialization_exists_principal_degZero_forall_support_sub_inertia_smul_eq_of_splitting.lean

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

theorem ModularCurve.JHPlaceSpecialization.exists_principal_degZero_forall_support_sub_inertia_smul_eq_of_splitting
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

    (hsplit : ∀ (X : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)))),
      (∀ σ ∈ A.inertiaSubgroupIn ℚ, (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) = X) →
      (∀ V ∈ (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)).support, (Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ V ∨ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ V ∨ ∃ s ∈ SS, Psp.reduceFst α hα V = s.1)) →
      ∃ (D₁ D₂ : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)))),
        (∀ V ∈ (D₁ : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)).support,
          (∀ σ ∈ A.inertiaSubgroupIn ℚ, (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • V = V) ∧ (Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ V ∨ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ V ∨ ∃ s ∈ SS, Psp.reduceFst α hα V = s.1)) ∧
        Psp.IsGoodDiv α (θ.toAlgHom.comp α) hα hβ δ (D₂ : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) ∧
        (∃ hadm : Psp.glueData α (θ.toAlgHom.comp α) hα hβ δ SS (D₂ : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) ∈ GluingData.admissible SS,
          GluedPic0.mk SS ⟨Psp.glueData α (θ.toAlgHom.comp α) hα hβ δ SS (D₂ : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), hadm⟩ = 0) ∧
        ((X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) - D₁ - D₂) ∈ Divisor.principal (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)))
    (E : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (hEst : ∀ σ ∈ A.inertiaSubgroupIn ℚ, (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • E = E)
    (hEgood : ∀ V ∈ E.support, (Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ V ∨ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ V ∨ ∃ s ∈ SS, Psp.reduceFst α hα V = s.1)) :
    ∃ C : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
      C ∈ Divisor.principal (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)) ∧
      C ∈ Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)) ∧
      ∀ V ∈ (E - C).support,
        (∀ σ ∈ A.inertiaSubgroupIn ℚ, (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • V = V) ∧ (Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ V ∨ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ V ∨ ∃ s ∈ SS, Psp.reduceFst α hα V = s.1) := by sorry
