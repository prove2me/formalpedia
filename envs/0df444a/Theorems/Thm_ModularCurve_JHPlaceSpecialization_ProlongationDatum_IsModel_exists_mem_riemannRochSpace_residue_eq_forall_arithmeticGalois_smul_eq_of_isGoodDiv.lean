-- Prove2me | Theorems.Thm_ModularCurve_JHPlaceSpecialization_ProlongationDatum_IsModel_exists_mem_riemannRochSpace_residue_eq_forall_arithmeticGalois_smul_eq_of_isGoodDiv
-- name    : ModularCurve.JHPlaceSpecialization.ProlongationDatum.IsModel.exists_mem_riemannRochSpace_residue_eq_forall_arithmeticGalois_smul_eq_of_isGoodDiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/1b3d1daf-3e89-558d-96d4-31d2351f949c
-- title:
--   Galois-equivariant bi-integral lift of node-compatible residue pairs
-- statement:
--   Throughout, $p$ is a prime with $p \mid M$ and $p^2 \nmid M$, and $H \le (\mathbb{Z}/M)^\times$ is a subgroup containing every unit that becomes $1$ in $(\mathbb{Z}/(M/p))^\times$ (hypothesis `hHp`). Furthermore $A$ is a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` with `A.LiesOverPrime p`, i.e. $p$ is a non-unit of $A$, whose residue field $\kappa =$ `ResidueField ↥A` is algebraically closed of characteristic $p$. Write $F =$ `xHFunctionFieldBar M H` for the base change to $\overline{\mathbb{Q}}$ of the function field of $X_H(M)$ inside Laurent series, $F' =$ `xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)` for the corresponding field at level $M/p$ with $H$ replaced by its image `infSubgroup p M H hpM` under reduction, and $\bar F =$ `Fbar p M H hpM (ResidueField ↥A)` $=$ `qExpFunctionFieldC κ (ΓN p M H hpM)` for the characteristic-$p$ function field of the fibre, of genus $g =$ `genusFF κ Fbar`.
--
--   The data are: a $\overline{\mathbb{Q}}$-algebra automorphism $\theta$ of $F$; an integral $\overline{\mathbb{Q}}$-algebra map $\alpha : F' \to F$ (hypothesis `hα`) with $\beta = \theta \circ \alpha$ also integral (`hβ`), normalised on $q$-expansions by `hα_coe` ($\alpha$ is the inclusion of Laurent series) and by `hβ_coe` ($\beta$ is $q \mapsto q^p$, i.e. composition with `qExpand (AlgebraicClosure ℚ) p`); a unit $pb$ of $\mathbb{Z}/(M/p)$ whose underlying residue is $p$ (`hpb`); a self-map $\delta$ of the places of $\bar F$ over $\kappa$, which by `hδ` is the action on places of the semilinear automorphism `SemilinearAut.ofAlgAut` attached to `diamondActionModL` evaluated at a $\Gamma_0(M/p)$-lift [`CuspForm.gammaLift (M / p) pb`](def/CuspForm_HeckeOperatorFormsGammaH.html#L36) of $pb$; a finite set $SS$ of pairs of places of $\bar F$ which by `hSS` enumerates `ssNodePairsQExp`, that is the pairs $(s_1, s_2)$ with $s_2$ a supersingular place and $s_1 =$ `qExpFrobeniusPlaceModL` of $s_2$; a place-specialization datum $Psp$ of type `JHPlaceSpecialization p M H hpM A`, consisting of a map `sp` from places of $F'$ to places of $\bar F$ together with a map on $\mathrm{Pic}^0$ and the compatibilities recorded in that structure; and a prolongation datum $Rpd$ for $Psp$ and $\theta$, consisting of two regular prolongations $R_1, R_2$ of $A$ to $F$ with residue field $\bar F$, related by $f \in R_2.\mathrm{integers} \iff \theta f \in R_1.\mathrm{integers}$ and $\mathrm{res}_2(f) = \mathrm{res}_1(\theta f)$. Here `Psp.reduceFst α hα W` is `sp` applied to the restriction of $W$ along $\alpha$, and `Psp.reduceSnd β hβ δ W` is $\delta$ applied to `sp` of the restriction of $W$ along $\beta$; a place $W$ of $F$ is strict of the first kind (`IsStrictFst`) when $\delta(\mathrm{Frob}(\mathrm{red}_1 W)) = \mathrm{red}_2 W$ and $\mathrm{red}_1 W$ is not $\delta$-fixed, and strict of the second kind (`IsStrictSnd`) when $\mathrm{red}_1 W = \mathrm{Frob}(\mathrm{red}_2 W)$ and $\mathrm{red}_2 W$ is not $\delta$-fixed, where $\mathrm{Frob}$ is `qExpFrobeniusPlaceModL` and a place $v$ of $\bar F$ is $\delta$-fixed (`Fixed`) when $\mathrm{Frob}(\delta(\mathrm{Frob}\, v)) = v$.
--
--   The hypotheses on this frame are the following groups.
--
--   Fixed-point and dichotomy hypotheses: `hFix` asserts that every supersingular place $y$ (member of `ssPlacesQExp`) and also $\mathrm{Frob}\, y$ are $\delta$-fixed; `hTD` (`TypeDichotomy`) asserts that every place $W$ of $F$ satisfies $\mathrm{red}_1 W = \mathrm{Frob}(\mathrm{red}_2 W)$ or $\delta(\mathrm{Frob}(\mathrm{red}_1 W)) = \mathrm{red}_2 W$; `hFixFin` asserts that the set of $\delta$-fixed places of $\bar F$ is finite.
--
--   The model laws: `hmodel` is `IsModel`, the conjunction of the four laws `DivisorLawFst`, `DivisorLawSnd`, `CuspLawInfty` and `CuspLawZero` for $R_1, R_2$; `hO` (`OrderLawFixed`) states that for $f$ lying in both rings of integers with both residues non-zero, and $D'$ the divisor of $f$, every $\delta$-fixed affine place $v$ (affine in the sense of `IsAffinePlace`: the function with $q$-expansion `jqModC` has a value at $v$) satisfies $(\mathrm{red}_1)_*D'(v) = \mathrm{ord}_v(\mathrm{res}_1 f) + \mathrm{ord}_{\delta(\mathrm{Frob}\,v)}(\mathrm{res}_2 f)$; `hreg` (`RegularityLaw`) has two clauses: for $f$ in both rings of integers and $v$ a $\delta$-fixed affine place such that $\mathrm{ord}_V f \ge 0$ for all $V$ with $\mathrm{red}_1 V = v$, the residues are regular at $v$ and at $\delta(\mathrm{Frob}\, v)$ respectively when non-zero, and for $s \in SS$ with $\mathrm{ord}_V f \ge 0$ for all $V$ with $\mathrm{red}_1 V = s_1$ there is $c \in \kappa$ which is the value of $\mathrm{res}_1 f$ at $s_1$ and of $\mathrm{res}_2 f$ at $s_2$; `hnv` (`NodeValueLaw`) states that for $f$ in both rings with non-zero residues and $s \in SS$ such that no place $V$ with $\mathrm{ord}_V f \neq 0$ reduces to $(s_1, s_2)$, there is a non-zero $c \in \kappa$ which is simultaneously the value of $\mathrm{res}_1 f$ at $s_1$ and of $\mathrm{res}_2 f$ at $s_2$.
--
--   Equivariance: `hθgal` asserts that $\theta$ commutes with the action of every $\sigma \in \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ through `arithmeticGalois (xHFunctionField M H)`.
--
--   Two-pole hypotheses `hLFst` and `hLSnd`: `hLFst` requires that whenever $Q \neq Q'$ are strict places of the first kind with the same image $v = \mathrm{red}_1 Q = \mathrm{red}_1 Q'$, $v$ affine, $n$ a natural number with $n \neq 0$ in $\kappa$, $g \in R_1.\mathrm{integers}$ with $\mathrm{res}_1 g \neq 0$, $\mathrm{ord}_Q g = -n$, $\mathrm{ord}_{Q'} g = n$ and $\mathrm{ord}_W g = 0$ for every other strict first-kind place $W$ above $v$, and whenever $g = 1 + e\varepsilon$ with $e \in A$ and $\varepsilon \in R_1.\mathrm{integers}$ of non-zero residue, then $\mathrm{ord}_v(\mathrm{res}_1 \varepsilon) \ge -1$; `hLSnd` is the mirror statement for strict places of the second kind, $\mathrm{red}_2$ and $R_2$.
--
--   Unit hypothesis `hUnit`: there exist $u_1, u_2 \in F$ and divisors $D_1, D_2$ with $D_i = \mathrm{div}(u_i)$ pointwise, such that $u_1$ and $u_1^{-1}$ lie in $R_1.\mathrm{integers}$ with $\mathrm{res}_1 u_1 \neq 0$, the push-forward along $\mathrm{red}_1$ of the strict first-kind part `Psp.fstDiv … D₁` agrees with $\mathrm{ord}_v(\mathrm{res}_1 u_1)$ at every place $v$ of $\bar F$ that is not $\delta$-fixed, and the push-forward along $\mathrm{red}_1$ of $D_1$ restricted to the infinity-side places agrees with $\mathrm{ord}_{\mathrm{red}_1 C}(\mathrm{res}_1 u_1)$ at $\mathrm{red}_1 C$ for every infinity-side place $C$; symmetrically for $u_2$, $R_2$, $\mathrm{red}_2$, `Psp.sndDiv` and the zero-side places; together with the two cofinality clauses that every non-zero $f \in F$ admits $m \neq 0$ and $j \in \mathbb{Z}$ with $f^m u_1^{j} \in R_2.\mathrm{integers}$ of non-zero residue, and likewise $f^m u_2^{j} \in R_1.\mathrm{integers}$ of non-zero residue. Here `IsInftySide C` means that $C$ is cuspidal and that $x'/x^p$ has at $C$ a value in $A$ with residue $1$, where $x, x'$ have $q$-expansions `jqModC` and its $q \mapsto q^p$ substitute, and `IsZeroSide C` is the analogous condition for $x/x'^p$ with the other cuspidality predicate.
--
--   Cusp and orientation hypotheses: `hcusp` asserts that every non-affine place $w$ of $\bar F$ is $\mathrm{red}_1$ of some infinity-side place and $\mathrm{red}_2$ of some zero-side place; `horientInf` asserts $\delta(\mathrm{Frob}(\mathrm{red}_1 C)) = \mathrm{red}_2 C$ for infinity-side $C$, and `horient0` asserts $\mathrm{red}_1 C = \mathrm{Frob}(\mathrm{red}_2 C)$ for zero-side $C$.
--
--   Annulus hypotheses: a function $e$ on $SS$ with $e(s) > 0$ (`he`), and `hAnn`, which provides for each $s \in SS$ an annulus $An$ over $A$ in $F$ (an [`AlgebraicCurve.Annulus`](def/AlgebraicCurve_SemistableCharts.html#L86): a set `dom` of rational places faithfully parametrised by the values of a coordinate `param` running through the elements of the maximal ideal of $A$ dividing a `modulus`, with $\mathrm{ord}_P(\mathrm{param} - \mathrm{param}(P)) = 1$ and a unit principle) subject to six clauses: `An.dom` consists exactly of the places $W$ with $\mathrm{red}_1 W = s_1$ that are strict of neither kind; $An.\mathrm{modulus} = p^{e(s)}u$ for a unit $u$ of $A$; `An.param` is fixed by `arithmeticGalois` for every $\sigma$ in the inertia subgroup `A.inertiaSubgroupIn ℚ`; $\mathrm{modulus}^{-1}\cdot\mathrm{param}$ lies in $R_1.\mathrm{integers}$; $\mathrm{param}$ lies in $R_2.\mathrm{integers}$ with non-zero residue; and two normalisation clauses stating that $\mathrm{ord}_{s_2}(\mathrm{res}_2 \mathrm{param}) = 1$, respectively $\mathrm{ord}_{s_1}(\mathrm{res}_1(\mathrm{modulus}\cdot\mathrm{param}^{-1})) = 1$, each accompanied by the assertion that for $f$ in the corresponding ring of integers with non-zero residue and $\mathrm{ord}_P f = 0$ on the annulus, the value at each $P \in An.\mathrm{dom}$ of $f$ times the corresponding coordinate raised to $-\mathrm{ord}_{s_i}(\mathrm{res}_i f)$ lies in $A$ and is a unit there.
--
--   Finally, the data of the conclusion: a set $S$ of automorphisms $\sigma$ of $\overline{\mathbb{Q}}$ over $\mathbb{Q}$, each lying in `A.inertiaSubgroupIn ℚ` (`hS`); a divisor $D$ on $F$ with $D \ge 0$ (`hD`) which is good (`hgood`: every place in the support of $D$ is strict of the first or of the second kind) and whose support is pointwise fixed by the action of every $\sigma \in S$ (`hDfix`); the degree bounds $2g - 1 + \#SS \le \deg (\mathrm{red}_1)_*(\mathrm{fstDiv}\, D)$ (`hdeg₁`) and $2g - 1 \le \deg (\mathrm{red}_2)_*(\mathrm{sndDiv}\, D)$ (`hdeg₂`); elements $g_1, g_2 \in \bar F$ lying in the Riemann–Roch spaces of $(\mathrm{red}_1)_*(\mathrm{fstDiv}\, D)$ and of $(\mathrm{red}_2)_*(\mathrm{sndDiv}\, D)$ respectively; and the node compatibility `hnode`: for each $s \in SS$ there is $c \in \kappa$ such that $g_1$ has value $c$ at $s_1$ and $g_2$ has value $c$ at $s_2$.
--
--   Under all of these, the conclusion is the existence of an element $G \in F$ which lies in $R_1.\mathrm{integers}$ and in $R_2.\mathrm{integers}$ and satisfies: $G \in$ `riemannRochSpace D`, that is $\mathrm{ord}_v G \ge -D(v)$ for every place $v$ of $F$; $R_1$-residue of $G$ equal to $g_1$; $R_2$-residue of $G$ equal to $g_2$; and $\sigma \cdot G = G$, for the `arithmeticGalois` action, for every $\sigma \in S$.
--
--   This is the gluing step for the two components of the semistable fibre: a pair of functions on the reduction, one on each component, matching at the supersingular nodes, is realised as the reduction of a single function in the Riemann–Roch space of a good divisor upstairs, with integrality for both prolongations and invariance under the prescribed inertia elements. It is used in the construction of a function with a prescribed simple zero and controlled strict behaviour that is inertia-invariant, in the analysis of $X_H(M)$ at a prime exactly dividing the level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHPlaceSpecialization_ProlongationDatum_IsModel_exists_mem_riemannRochSpace_residue_eq_forall_arithmeticGalois_smul_eq_of_isGoodDiv.lean

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_AdelicIndex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing ModularCurve.JHNeronObjectAtP
open AlgebraicCurve
open ModularCurve
open scoped MatrixGroups

open Classical in

theorem ModularCurve.JHPlaceSpecialization.ProlongationDatum.IsModel.exists_mem_riemannRochSpace_residue_eq_forall_arithmeticGalois_smul_eq_of_isGoodDiv
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
    (S : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (hS : ∀ σ ∈ S, σ ∈ A.inertiaSubgroupIn ℚ)
    (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (hD : 0 ≤ D) (hgood : Psp.IsGoodDiv α (θ.toAlgHom.comp α) hα hβ δ D)
    (hDfix : ∀ V ∈ D.support, ∀ σ ∈ S, (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • V = V)
    (hdeg₁ : 2 * (genusFF (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) : ℤ) - 1 + SS.card ≤
      (Finsupp.mapDomain (Psp.reduceFst α hα) (Psp.fstDiv α (θ.toAlgHom.comp α) hα hβ δ D)).degree)
    (hdeg₂ : 2 * (genusFF (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) : ℤ) - 1 ≤
      (Finsupp.mapDomain (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ) (Psp.sndDiv α (θ.toAlgHom.comp α) hα hβ δ D)).degree)
    (g₁ g₂ : (Fbar p M H hpM (ResidueField ↥A)))
    (hg₁ : g₁ ∈ riemannRochSpace (Finsupp.mapDomain (Psp.reduceFst α hα) (Psp.fstDiv α (θ.toAlgHom.comp α) hα hβ δ D)))
    (hg₂ : g₂ ∈ riemannRochSpace (Finsupp.mapDomain (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ) (Psp.sndDiv α (θ.toAlgHom.comp α) hα hβ δ D)))
    (hnode : ∀ s ∈ SS, ∃ c : ResidueField ↥A, s.1.HasValue g₁ c ∧ s.2.HasValue g₂ c) :
    ∃ (G : ↥(xHFunctionFieldBar M H)) (h₁ : G ∈ Rpd.R₁.integers) (h₂ : G ∈ Rpd.R₂.integers),
      G ∈ riemannRochSpace D ∧ Rpd.R₁.residue ⟨G, h₁⟩ = g₁ ∧ Rpd.R₂.residue ⟨G, h₂⟩ = g₂ ∧
        ∀ σ ∈ S, (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • G = G := by sorry
