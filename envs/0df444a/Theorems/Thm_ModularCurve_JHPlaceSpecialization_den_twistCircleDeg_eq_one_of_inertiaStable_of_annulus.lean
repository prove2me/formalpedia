-- Prove2me | Theorems.Thm_ModularCurve_JHPlaceSpecialization_den_twistCircleDeg_eq_one_of_inertiaStable_of_annulus
-- name    : ModularCurve.JHPlaceSpecialization.den_twistCircleDeg_eq_one_of_inertiaStable_of_annulus
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/9673491c-a047-5267-8097-2c0dea1b84a5
-- title:
--   Tent-weighted circle degrees of inertia-stable divisors are integers
-- statement:
--   Throughout, $\kappa$ denotes the residue field of $A$, $F_M$ the field `xHFunctionFieldBar M H` (the base change to $\overline{\mathbb Q}$, inside Laurent series, of the function field `xHFunctionField M H` of $X_H(M)$), $F_{M/p}$ the corresponding field `xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)` at level $M/p$ for the image subgroup `infSubgroup p M H hpM` $=$ image of $H$ under `ZMod.unitsMap`, and $\bar F$ the field `Fbar p M H hpM κ` $=$ `qExpFunctionFieldC κ (ΓN p M H hpM)`. Places are in the sense of [`AlgebraicCurve.Place`](def/AlgebraicCurve_DivisorClassGroup.html#L22): valuation subrings containing the base field, proper and with principal ideals, with normalised order function `ord`, degree `deg`, and `HasValue g a` meaning that $g$ lies in the valuation ring and has residue $a$. Write $\Phi$ for `qExpFrobeniusPlaceModL κ (ΓN p M H hpM) p`, the pullback of a place of $\bar F$ along the $p$-power Frobenius of the characteristic-$p$ $q$-expansion function field.
--
--   Arithmetic data. A prime $p$ and $M \neq 0$ with $p \mid M$ (`hpM`) and $p^2 \nmid M$ (`hpM2`); a subgroup $H \le (\mathbb Z/M)^\times$ such that every unit mapping to $1$ in $(\mathbb Z/(M/p))^\times$ lies in $H$ (`hHp`); $M/p \neq 0$. A valuation subring $A$ of $\overline{\mathbb Q}$ with $p$ a non-unit of $A$ (`hA`, i.e. `A.LiesOverPrime p`), whose residue field $\kappa$ has characteristic $p$ and is algebraically closed.
--
--   Degeneracy data. An automorphism $\theta$ of $F_M$ over $\overline{\mathbb Q}$; an $\overline{\mathbb Q}$-algebra map $\alpha : F_{M/p} \to F_M$ which is integral (`hα`) and is the identity on underlying Laurent series (`hα_coe`); the composite $\beta$ of $\alpha$ followed by $\theta$ is integral (`hβ`) and acts on Laurent series by $q \mapsto q^p$, i.e. the Laurent series of $\beta(u)$ is `qExpand (AlgebraicClosure ℚ) p` applied to that of $u$ (`hβ_coe`); and $\theta$ commutes with the semilinear action `arithmeticGalois` of every $\sigma \in \mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ on $F_M$ (`hθgal`).
--
--   Diamond operator and nodes. A unit `pb` of $\mathbb Z/(M/p)$ whose underlying residue is $p$ (`hpb`); a self-map $\delta$ of the places of $\bar F$ given by the action of the semilinear automorphism `SemilinearAut.ofAlgAut` attached to the diamond automorphism `diamondActionModL κ (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)` (`hδ`). A finite set $SS$ of pairs of places of $\bar F$ whose elements are exactly the members of `ssNodePairsQExp κ (ΓN p M H hpM) p` (`hSS`), that is, pairs $s$ with $s_2$ a supersingular place and $s_1 = \Phi(s_2)$.
--
--   Specialisation and prolongation. A `JHPlaceSpecialization p M H hpM A`, written `Psp`: a surjective specialisation map `sp` from places of $F_{M/p}$ to places of $\bar F$ together with a homomorphism on degree-zero divisor classes, subject to the $q$-expansion, divisor, inertia and Frobenius compatibilities of that structure. A `ProlongationDatum Psp θ`, written `Rpd`: two regular prolongations $R_1, R_2$ of $A$ to $F_M$ with residue maps onto $\bar F$, with the $q$-expansion compatibility for $R_1$, and with $f \in R_2$ integral iff $\theta f \in R_1$ integral and matching residues. For a place $W$ of $F_M$, `reduceFst` is `sp` applied to the restriction of $W$ along $\alpha$, and `reduceSnd` is $\delta$ applied to `sp` of the restriction of $W$ along $\beta$; $W$ is strict on the first side when $\delta(\Phi(\mathrm{red}_1 W)) = \mathrm{red}_2 W$ and $\mathrm{red}_1 W$ is not $\delta$-fixed, and strict on the second side when $\mathrm{red}_1 W = \Phi(\mathrm{red}_2 W)$ and $\mathrm{red}_2 W$ is not $\delta$-fixed; a place $v$ of $\bar F$ is $\delta$-fixed when $\Phi(\delta(\Phi v)) = v$.
--
--   Hypotheses on the reduction pattern. `hFix`: for every supersingular place $y$ in `ssPlacesQExp κ (ΓN p M H hpM) p`, both $y$ and $\Phi y$ are $\delta$-fixed. `hFixFin`: the set of $\delta$-fixed places of $\bar F$ is finite. `hTD`: for every place $W$ of $F_M$, either $\mathrm{red}_1 W = \Phi(\mathrm{red}_2 W)$ or $\delta(\Phi(\mathrm{red}_1 W)) = \mathrm{red}_2 W$. `hmodel`: `Rpd.IsModel`, the conjunction of the two divisor laws and of the cusp laws at $\infty$ and at $0$. `hO`: the order law at $\delta$-fixed affine places, namely that for $f$ integral for both prolongations with nonzero residues and $D$ the divisor of $f$, the pushforward of $D$ along `reduceFst` at such a place $v$ equals $v.\mathrm{ord}$ of the $R_1$-residue plus $(\delta(\Phi v)).\mathrm{ord}$ of the $R_2$-residue. `hreg`: the regularity law relative to $SS$ (non-negativity of the two residue orders at $\delta$-fixed affine places, and existence of common values at the pairs in $SS$, for functions with no poles above the relevant place). `hnv`: the node value law relative to $SS$ (for $f$ integral for both prolongations with nonzero residues and $s \in SS$ such that no place with $\mathrm{ord}\, f \neq 0$ reduces to $s$ on both sides, the two residues take a common nonzero value at $s_1$ and $s_2$). `hcusp`: every place of $\bar F$ that is not an affine place (no function of $\bar F$ with $q$-expansion `jqModC κ` taking a value there) is both `reduceFst` of some place of $F_M$ on the $\infty$-side and `reduceSnd` of some place on the $0$-side. `horientInf`: for every $\infty$-side place $C$, $\delta(\Phi(\mathrm{red}_1 C)) = \mathrm{red}_2 C$. `horient0`: for every $0$-side place $C$, $\mathrm{red}_1 C = \Phi(\mathrm{red}_2 C)$.
--
--   Local bounds at double points. `hLFst`: for all places $Q \neq Q'$ of $F_M$ strict on the first side with $\mathrm{red}_1 Q' = \mathrm{red}_1 Q$ and $\mathrm{red}_1 Q$ an affine place, for every natural $n$ nonzero in $\kappa$, every $g$ integral for $R_1$ with nonzero residue such that $\mathrm{ord}_Q g = -n$, $\mathrm{ord}_{Q'} g = n$ and $\mathrm{ord}_W g = 0$ for every further first-side strict place $W$ with $\mathrm{red}_1 W = \mathrm{red}_1 Q$, and for every $a \in A$ and every $\varepsilon$ integral for $R_1$ with nonzero residue such that $g = 1 + a\varepsilon$, one has $(\mathrm{red}_1 Q).\mathrm{ord}$ of the $R_1$-residue of $\varepsilon$ at least $-1$. `hLSnd`: the mirror statement with `IsStrictSnd`, `reduceSnd` and $R_2$ in place of `IsStrictFst`, `reduceFst` and $R_1$.
--
--   Units. `hUnit`: there are $u_1, u_2 \in F_M$ and divisors $D_1, D_2$ of $F_M$ with $D_i(W) = \mathrm{ord}_W u_i$ for all $W$, such that: $u_1$ and $u_1^{-1}$ are integral for $R_1$ with $R_1$-residue of $u_1$ nonzero, the pushforward along `reduceFst` of the first-side part $D_1$ (the restriction of $D_1$ to the first-side strict places) agrees at every non-$\delta$-fixed place $v$ of $\bar F$ with $v.\mathrm{ord}$ of the $R_1$-residue of $u_1$, and the pushforward along `reduceFst` of the restriction of $D_1$ to the $\infty$-side places agrees at $\mathrm{red}_1 C$, for every $\infty$-side place $C$, with $(\mathrm{red}_1 C).\mathrm{ord}$ of that residue; for every nonzero $f \in F_M$ there are $m \neq 0$ in $\mathbb N$ and $j \in \mathbb Z$ with $f^m u_1^{\,j}$ integral for $R_2$ with nonzero residue; and symmetrically for $u_2$, with $R_2$, the second-side part of $D_2$, the $0$-side places and `reduceSnd`, together with the existence for each nonzero $f$ of $m \neq 0$ and $j$ with $f^m u_2^{\,j}$ integral for $R_1$ with nonzero residue.
--
--   Annulus block. A function $e : SS \to \mathbb N$ with $e(s) > 0$ for all $s$ (`he`). The hypothesis `hAnn` asserts, for each $s \in SS$, the existence of an annulus of $F_M$ along $A$ (in the sense of the structure [`AlgebraicCurve.Annulus`](def/AlgebraicCurve_SemistableCharts.html#L86): a set of places, a parameter, a modulus in the maximal ideal of $A$, with the rationality, evaluation, uniqueness, order and unit axioms of that structure) whose domain consists exactly of the places $W$ with $\mathrm{red}_1 W = s_1$ that are strict on neither side, whose modulus is $p^{e(s)}$ times a unit of $A$, whose parameter is fixed by the `arithmeticGalois` action of every $\sigma$ in the inertia subgroup `A.inertiaSubgroupIn ℚ`, which satisfies: modulus$^{-1}\cdot$parameter is integral for $R_1$; the parameter is integral for $R_2$ with nonzero residue and with $s_2.\mathrm{ord}$ of that residue equal to $1$, together with the unit principle on the annulus for $R_2$-integral functions with nonzero residue and no zeros or poles on the annulus; and modulus$\cdot$parameter$^{-1}$ is integral for $R_1$ with $s_1.\mathrm{ord}$ of its residue equal to $1$, together with the corresponding unit principle for $R_1$. The data `An` is a chosen family of such annuli, `hAn` requiring of each `An s` exactly the list of properties just described.
--
--   Positions. A function `pos` assigning to each $s \in SS$ and each place of $F_M$ a rational number, subject to `hpos`, the position law `AnnulusPositionLaw SS e An pos`: for every $s$ and every place $V$ in the domain of `An s`, $0 < \mathrm{pos}_s(V) < e(s)$ and $A$'s valuation of $V$'s evaluation at modulus$\cdot$parameter$^{-1}$, raised to the denominator of $\mathrm{pos}_s(V)$, equals $A$'s valuation of $p$ raised to the numerator of $\mathrm{pos}_s(V)$; and to `hposσ`, invariance $\mathrm{pos}_s(\sigma \cdot V) = \mathrm{pos}_s(V)$ for every $\sigma$ in `A.inertiaSubgroupIn ℚ` acting through `arithmeticGalois`.
--
--   Divisor. An element $X$ of `Divisor.degZero`, i.e. a finitely supported $\mathbb Z$-valued function on the places of $F_M$ over $\overline{\mathbb Q}$ of total degree zero, which is stable under the `arithmeticGalois` action of every $\sigma$ in `A.inertiaSubgroupIn ℚ` (`hXst`).
--
--   Conclusion: for every $s \in SS$ and every natural number $d$, the rational number `twistCircleDeg SS An pos X s d`, namely
--   $$\sum_{\substack{V \in \mathrm{supp}\,X \\ V \in (\mathrm{An}\,s).\mathrm{dom}}} X(V)\,\max\bigl(0,\ 1 - |\mathrm{pos}_s(V) - d|\bigr),$$
--   has denominator $1$, that is, it is an integer.
--
--   This is the integrality half of the circle-degree statement for $X_H(M)$ at a prime exactly dividing the level: the tent-weighted sums over the annulus at a supersingular node pair, formed from an inertia-stable degree-zero divisor, are the integral right-hand sides of the Dirichlet problems on the chains of the regular model that produce a twist vector. It is invoked by the downstream results on chord bounds and end orders, on coupled scalings, and on the existence of inertia-fixed differences of twist type.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHPlaceSpecialization_den_twistCircleDeg_eq_one_of_inertiaStable_of_annulus.lean

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

theorem ModularCurve.JHPlaceSpecialization.den_twistCircleDeg_eq_one_of_inertiaStable_of_annulus
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
    ∀ (s : ↥SS) (d : ℕ), (JHPlaceSpecialization.twistCircleDeg SS An pos (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) s d).den = 1 := by sorry
