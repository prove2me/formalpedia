-- Prove2me | Theorems.Thm_ModularCurve_JHPlaceSpecialization_exists_inertiaFixed_isTwistType_sub_of_inertiaStable_of_annulus
-- name    : ModularCurve.JHPlaceSpecialization.exists_inertiaFixed_isTwistType_sub_of_inertiaStable_of_annulus
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/a3a6324b-8754-5119-808a-441b54144934
-- title:
--   Twist type after subtracting an inertia-fixed divisor
-- statement:
--   Fix a prime $p$ and a natural number $M$ with $p \mid M$ (`hpM`) and $p^2 \nmid M$ (`hpM2`), and a subgroup $H \le (\mathbf{Z}/M)^\times$ containing every unit whose image under `ZMod.unitsMap` for $M/p \mid M$ is $1$ (`hHp`). Let $A$ be a valuation subring of $\overline{\mathbf{Q}} =$ `AlgebraicClosure ℚ` with `A.LiesOverPrime p`, that is $p$ is a non-unit of $A$ (`hA`), whose residue field $\kappa$ is of characteristic $p$ and algebraically closed. Write $F_M =$ `xHFunctionFieldBar M H` for the base change to $\overline{\mathbf{Q}}$ of the function field of $X_H(M)$ inside Laurent series, $F_{M/p} =$ `xHFunctionFieldBar (M/p) (infSubgroup p M H hpM)` for the corresponding field at level $M/p$ with the image subgroup `infSubgroup p M H hpM`, and $\mathrm{Fb} =$ `Fbar p M H hpM κ` for the characteristic-$p$ $q$-expansion function field at the level group `ΓN p M H hpM`. The data are: an $\overline{\mathbf{Q}}$-algebra automorphism $\theta$ of $F_M$; an $\overline{\mathbf{Q}}$-algebra map $\alpha : F_{M/p} \to F_M$ with $\alpha$ integral (`hα`) and $\theta \circ \alpha$ integral (`hβ`), where $\alpha$ is the identity on $q$-expansions (`hα_coe`) and $\theta \circ \alpha$ is the substitution $q \mapsto q^p$, i.e. `qExpand _ p`, on $q$-expansions (`hβ_coe`); a unit $pb$ of $\mathbf{Z}/(M/p)$ reducing to $p$ (`hpb`); the map $\delta$ on places of $\mathrm{Fb}$ given by the semilinear action of the diamond automorphism `diamondActionModL κ (M/p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M/p) pb)` (`hδ`); a finset $SS$ of pairs of places of $\mathrm{Fb}$ whose members are exactly the supersingular node pairs `ssNodePairsQExp κ (ΓN p M H hpM) p`, that is the pairs $s$ with $s_2$ supersingular and $s_1 = \Phi(s_2)$, where $\Phi =$ `qExpFrobeniusPlaceModL κ (ΓN p M H hpM) p` (`hSS`); a place-specialisation datum `Psp : JHPlaceSpecialization p M H hpM A`; and a prolongation datum `Rpd` for `Psp` and $\theta$, consisting of two regular prolongations $R_1, R_2$ of $A$ in $F_M$ with values in $\mathrm{Fb}$, compatible through $\theta$. Throughout, $\mathrm{red}_1 W =$ `Psp.reduceFst α hα W` is the specialisation of the restriction of $W$ along $\alpha$, $\mathrm{red}_2 W =$ `Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ W` is $\delta$ applied to the specialisation of the restriction along $\theta \circ \alpha$, a place $v$ of $\mathrm{Fb}$ is $\delta$-fixed (`Fixed`) when $\Phi(\delta(\Phi v)) = v$, $W$ is strict of the first kind when $\delta(\Phi(\mathrm{red}_1 W)) = \mathrm{red}_2 W$ and $\mathrm{red}_1 W$ is not $\delta$-fixed, and strict of the second kind when $\mathrm{red}_1 W = \Phi(\mathrm{red}_2 W)$ and $\mathrm{red}_2 W$ is not $\delta$-fixed.
--
--   The specialisation laws assumed are: `hFix`, every supersingular place $y$ in `ssPlacesQExp κ (ΓN p M H hpM) p` is $\delta$-fixed and so is $\Phi y$; `hTD`, the type dichotomy, for every place $W$ of $F_M$ either $\mathrm{red}_1 W = \Phi(\mathrm{red}_2 W)$ or $\delta(\Phi(\mathrm{red}_1 W)) = \mathrm{red}_2 W$; `hmodel`, that `Rpd` is a model, i.e. the four laws `DivisorLawFst`, `DivisorLawSnd`, `CuspLawInfty`, `CuspLawZero` hold; `hO`, the order law at fixed places: for $f$ lying in the integers of both $R_1$ and $R_2$ with both residues non-zero, and $D$ the divisor of $f$, at every $\delta$-fixed affine place $v$ (affine meaning $v$ has a value at an element of $\mathrm{Fb}$ with $q$-expansion `jqModC κ`) the pushforward of $D$ along $\mathrm{red}_1$ at $v$ equals $\mathrm{ord}_v$ of the $R_1$-residue of $f$ plus $\mathrm{ord}_{\delta(\Phi v)}$ of the $R_2$-residue of $f$; `hreg`, the regularity law in two clauses, namely that $f$ with $\mathrm{ord}_V f \ge 0$ for all $V$ above a $\delta$-fixed affine place $v$ has residues of non-negative order at $v$ and at $\delta(\Phi v)$, and that $f$ with $\mathrm{ord}_V f \ge 0$ for all $V$ above $s_1$ has a common value $c \in \kappa$ of its two residues at $s_1$ and $s_2$ for every $s \in SS$; `hnv`, the node value law, that for $f$ as above whose divisor avoids the pair $s \in SS$ (no $V$ with $\mathrm{ord}_V f \neq 0$ has $\mathrm{red}_1 V = s_1$ and $\mathrm{red}_2 V = s_2$) the two residues take a common non-zero value at $s_1$ and $s_2$; `hθgal`, that $\theta$ commutes with the semilinear arithmetic Galois action `arithmeticGalois (xHFunctionField M H)` of every $\sigma \in \mathrm{Gal}(\overline{\mathbf{Q}}/\mathbf{Q})$; and `hFixFin`, that the set of $\delta$-fixed places of $\mathrm{Fb}$ is finite.
--
--   Two depth-one bounds are assumed, `hLFst` and `hLSnd`, of the same shape on the two sides. For `hLFst`: given places $Q \ne Q'$ of $F_M$, both strict of the first kind, with $\mathrm{red}_1 Q' = \mathrm{red}_1 Q$ an affine place, a natural number $n$ non-zero in $\kappa$, and $g$ in the integers of $R_1$ with non-zero residue such that $\mathrm{ord}_Q g = -n$, $\mathrm{ord}_{Q'} g = n$ and $\mathrm{ord}_W g = 0$ for every other strict place $W$ of the first kind with $\mathrm{red}_1 W = \mathrm{red}_1 Q$, and given $e \in A$ and $\varepsilon$ in the integers of $R_1$ with non-zero residue such that $g = 1 + e\varepsilon$, then $\mathrm{ord}_{\mathrm{red}_1 Q}$ of the $R_1$-residue of $\varepsilon$ is at least $-1$. The hypothesis `hLSnd` is the same statement with first kind replaced by second kind, $\mathrm{red}_1$ by $\mathrm{red}_2$ and $R_1$ by $R_2$.
--
--   The hypothesis `hUnit` posits elements $u_1, u_2$ of $F_M$ and divisors $D_1, D_2$ which are the divisors of $u_1$ and of $u_2$ ($D_i W = \mathrm{ord}_W u_i$ for all $W$), such that: $u_1$ and $u_1^{-1}$ lie in the integers of $R_1$ and the $R_1$-residue of $u_1$ is non-zero, the pushforward along $\mathrm{red}_1$ of the strict-first part of $D_1$ agrees at every place $v$ of $\mathrm{Fb}$ that is not $\delta$-fixed with $\mathrm{ord}_v$ of that residue, and the pushforward along $\mathrm{red}_1$ of the part of $D_1$ supported on the infinity-side places agrees at $\mathrm{red}_1 C$, for every infinity-side $C$, with $\mathrm{ord}_{\mathrm{red}_1 C}$ of that residue; every non-zero $f$ admits $m \neq 0$ and $j \in \mathbf{Z}$ with $f^m u_1^{\,j}$ in the integers of $R_2$ and of non-zero $R_2$-residue; and the mirror-image conditions for $u_2$, with $R_2$, $\mathrm{red}_2$, the strict-second part of $D_2$, the zero-side places, and $f^m u_2^{\,j}$ in the integers of $R_1$. Here an infinity-side place $C$ is a cuspidal place at which, for $x, x'$ of $q$-expansions `jqModC` and `qExpand _ p jqModC`, the function $x'/x^p$ takes a value $\tau \in A$ with residue $1$, and a zero-side place is the analogue for $x/x'^p$ with `IsCuspidal'`. Further, `hcusp` requires that every place $w$ of $\mathrm{Fb}$ that is not an affine place is both $\mathrm{red}_1$ of some infinity-side place and $\mathrm{red}_2$ of some zero-side place, while `horientInf` and `horient0` are the orientation conditions $\delta(\Phi(\mathrm{red}_1 C)) = \mathrm{red}_2 C$ for infinity-side $C$ and $\mathrm{red}_1 C = \Phi(\mathrm{red}_2 C)$ for zero-side $C$.
--
--   The annulus data consist of a function $e : SS \to \mathbf{N}$ with $e(s) > 0$ for all $s$ (`he`), a family $An$ of annuli [`AlgebraicCurve.Annulus A F_M`](def/AlgebraicCurve_SemistableCharts.html#L86) indexed by $SS$, and the requirements `hAnn` and `hAn`, which impose the same list of conditions in existential form and for the chosen family $An$ respectively: for each $s \in SS$, the domain of the annulus consists exactly of the places $W$ with $\mathrm{red}_1 W = s_1$ which are strict of neither kind; its modulus is $p^{e(s)}$ times a unit of $A$; its parameter is fixed by the arithmetic Galois action of every $\sigma$ in the inertia subgroup `A.inertiaSubgroupIn ℚ`; $(\text{modulus})^{-1}\cdot\text{param}$ lies in the integers of $R_1$; the parameter lies in the integers of $R_2$ with non-zero residue; the $R_2$-residue of the parameter has order $1$ at $s_2$, and for every $f$ in the integers of $R_2$ with non-zero residue and $\mathrm{ord}_P f = 0$ throughout the domain, at each $P$ of the domain the element $P(f)\cdot P(\text{param})^{-\mathrm{ord}_{s_2}(\text{res}_2 f)}$ (values taken by `Place.evalAt`) lies in $A$ and is a unit there; and symmetrically, $(\text{modulus})\cdot(\text{param})^{-1}$ lies in the integers of $R_1$, its $R_1$-residue has order $1$ at $s_1$, and the corresponding unit statement holds with $R_1$, $s_1$ and this element. A position function $pos : SS \to \{\text{places of } F_M\} \to \mathbf{Q}$ is given satisfying `hpos`, the annulus position law: for each $s$ and each $V$ in the domain of $An(s)$ one has $0 < pos(s,V) < e(s)$ and $A$-valuation equality $\mathrm{val}\big(V((\text{modulus})\cdot(\text{param})^{-1})\big)^{\mathrm{den}} = \mathrm{val}(p)^{\mathrm{num}}$ for the denominator and numerator of $pos(s,V)$; `hposσ`, invariance of $pos$ under the arithmetic Galois action of the inertia subgroup; and `hposD`, that for each $s$ and each integer $d$ with $0 < d < e(s)$ there is a place $V$ in the domain of $An(s)$ fixed by the inertia action with $pos(s,V) = d$.
--
--   Finally, let $X$ be a divisor of degree zero on $F_M$ (an element of `Divisor.degZero`) which is stable under the arithmetic Galois action of every $\sigma \in$ `A.inertiaSubgroupIn ℚ` (`hXst`) and whose support is admissible (`hXsupp`): every $V$ in the support of $X$ is strict of the first kind, or strict of the second kind, or satisfies $\mathrm{red}_1 V = s_1$ for some $s \in SS$.
--
--   The conclusion asserts the existence of a divisor $D_{\mathrm{fix}}$ of degree zero on $F_M$ such that, first, every $V$ in the support of $D_{\mathrm{fix}}$ is fixed by the arithmetic Galois action of every element of `A.inertiaSubgroupIn ℚ` and is strict of the first kind, or strict of the second kind, or satisfies $\mathrm{red}_1 V = s_1$ for some $s \in SS$; and second, `Psp.IsTwistType α (θ.toAlgHom.comp α) hα hβ δ SS e An pos` holds for $X - D_{\mathrm{fix}}$, that is there is a vector $a :$ `TwistVec ↥SS` for which the predicate `Psp.IsTwistOf α (θ.toAlgHom.comp α) hα hβ δ SS e An pos a` holds of the divisor $X - D_{\mathrm{fix}}$.
--
--   This is the level-$H$ form of the class-killing step in the analysis of the reduction of $X_H(M)$ at a prime $p$ exactly dividing $M$: an inertia-stable degree-zero divisor with support on strict places and on places lying over the first coordinate of a supersingular node pair becomes of twist type once a divisor with inertia-fixed support of the same three kinds is subtracted. It is used by [`ModularCurve.JHPlaceSpecialization.exists_rep_inertiaFixed_support_strict_or_node_of_mem_inertiaInvariants_of_annulus_of_fixReg`](thm.html#ModularCurve.JHPlaceSpecialization.exists_rep_inertiaFixed_support_strict_or_node_of_mem_inertiaInvariants_of_annulus_of_fixReg), which produces inertia-fixed representatives for inertia-invariant divisor classes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHPlaceSpecialization_exists_inertiaFixed_isTwistType_sub_of_inertiaStable_of_annulus.lean

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

theorem ModularCurve.JHPlaceSpecialization.exists_inertiaFixed_isTwistType_sub_of_inertiaStable_of_annulus
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
    (hposD : ∀ (s : ↥SS) (d : ℕ), 0 < d → d < e s → ∃ V ∈ (An s).dom,
      (∀ σ ∈ A.inertiaSubgroupIn ℚ, (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • V = V) ∧ pos s V = d)
    (X : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H))))
    (hXst : ∀ σ ∈ A.inertiaSubgroupIn ℚ, (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) = X)
    (hXsupp : ∀ V ∈ (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)).support,
      (Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ V ∨ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ V ∨ ∃ s ∈ SS, Psp.reduceFst α hα V = s.1))
    :
    ∃ Dfix : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H))),
      (∀ V ∈ (Dfix : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)).support,
        (∀ σ ∈ A.inertiaSubgroupIn ℚ, (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • V = V) ∧
        (Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ V ∨ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ V ∨ ∃ s ∈ SS, Psp.reduceFst α hα V = s.1)) ∧
      Psp.IsTwistType α (θ.toAlgHom.comp α) hα hβ δ SS e An pos ((X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) - Dfix) := by sorry
