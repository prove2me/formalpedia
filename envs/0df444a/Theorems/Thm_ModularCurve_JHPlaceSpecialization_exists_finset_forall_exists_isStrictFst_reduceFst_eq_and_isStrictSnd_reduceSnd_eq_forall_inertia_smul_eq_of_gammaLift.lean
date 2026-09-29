-- Prove2me | Theorems.Thm_ModularCurve_JHPlaceSpecialization_exists_finset_forall_exists_isStrictFst_reduceFst_eq_and_isStrictSnd_reduceSnd_eq_forall_inertia_smul_eq_of_gammaLift
-- name    : ModularCurve.JHPlaceSpecialization.exists_finset_forall_exists_isStrictFst_reduceFst_eq_and_isStrictSnd_reduceSnd_eq_forall_inertia_smul_eq_of_gammaLift
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/95a4ce06-0a60-5cab-8231-7b757b897f60
-- title:
--   Inertia-fixed strict places with prescribed reduction, off finitely many
-- statement:
--   Throughout, $p$ is a prime and $M$ a nonzero natural number with $p \mid M$ but $p^2 \nmid M$ (hypotheses `hpM`, `hpM2`), $H$ is a subgroup of $(\mathbb{Z}/M)^\times$ containing every unit that reduces to $1$ in $(\mathbb{Z}/(M/p))^\times$ (hypothesis `hHp`), and $M/p$ is nonzero. Further, $A$ is a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` lying over $p$ in the sense of [`ValuationSubring.LiesOverPrime`](def/FLTPrelim_Ramification.html#L16), i.e. $p$ belongs to the nonunits of $A$, and its residue field $\kappa =$ `ResidueField ↥A` is algebraically closed of characteristic $p$.
--
--   Write $F_M$ for `xHFunctionFieldBar M H`, the compositum of $\overline{\mathbb{Q}}$ with the function field `xHFunctionField M H` inside Laurent series, $F_{M/p}$ for the corresponding field at level $M/p$ with subgroup `infSubgroup p M H hpM` (the image of $H$ under reduction $(\mathbb{Z}/M)^\times \to (\mathbb{Z}/(M/p))^\times$), and $\bar F$ for `JHNeronObjectAtP.Fbar p M H hpM κ`, the $q$-expansion function field over $\kappa$ for the group `JHNeronObjectAtP.ΓN p M H hpM`. Places are in the sense of [`AlgebraicCurve.Place`](def/AlgebraicCurve_DivisorClassGroup.html#L22): valuation subrings containing the base field, proper and with principal maximal ideal, with their order function `Place.ord` and value predicate `Place.HasValue`.
--
--   The data are: a $\overline{\mathbb{Q}}$-algebra automorphism $\theta$ of $F_M$; two integral $\overline{\mathbb{Q}}$-algebra maps $\alpha, \beta \colon F_{M/p} \to F_M$ (integrality being `hα`, `hβ`); a unit $pb$ of $\mathbb{Z}/(M/p)$ whose underlying residue class is $p$ (`hpb`); a self-map $\delta$ of the set of places of $\bar F$ over $\kappa$, required by `hδ` to be the action of the semilinear automorphism attached by `SemilinearAut.ofAlgAut` to the diamond automorphism `diamondActionModL κ (M/p) (infSubgroup p M H hpM)` evaluated at the lift [`CuspForm.gammaLift (M/p) pb`](def/CuspForm_HeckeOperatorFormsGammaH.html#L36) of $pb$ to $\Gamma_0(M/p)$; and a finite set $SS$ of pairs of places of $\bar F$ which, by `hSS`, is exactly `ssNodePairsQExp κ (JHNeronObjectAtP.ΓN p M H hpM) p`, i.e. the set of pairs $s$ whose second entry is a supersingular place and whose first entry is its image under the Frobenius map `qExpFrobeniusPlaceModL` on places.
--
--   The specialisation data are a `JHPlaceSpecialization p M H hpM A`, written $P$, consisting of a surjective map $\mathrm{sp}$ from places of $F_{M/p}$ to places of $\bar F$ together with a map on degree-zero divisor classes and the compatibilities recorded in that structure ($q$-expansion compatibility of divisor pushforward, existence of functions realising pushed-forward principal divisors, invariance of $\mathrm{sp}$ under the inertia subgroup of $A$, its Frobenius twist under Frobenius elements, and compatibility on $\mathrm{Pic}^0$), and a `ProlongationDatum` $R$ for $P$ and $\theta$: two regular prolongations $R_1, R_2$ of $A$ to $F_M$ with residue maps to $\bar F$, the $q$-expansion formula for $R_1$-residues, and the statement that $R_2$-integrality and $R_2$-residues are obtained from those of $R_1$ by precomposing with $\theta$. Here $P.\mathrm{reduceFst}\,\alpha$ sends a place $W$ of $F_M$ to $\mathrm{sp}$ of its restriction along $\alpha$, and $P.\mathrm{reduceSnd}\,\beta\,\delta$ sends $W$ to $\delta$ applied to $\mathrm{sp}$ of its restriction along $\beta$; a place $W$ is strict of the first kind (`IsStrictFst`) when $\delta(\mathrm{Frob}(\mathrm{reduceFst}\,W)) = \mathrm{reduceSnd}\,W$ and $\mathrm{reduceFst}\,W$ is not $\delta$-`Fixed` (fixedness of $v$ meaning $\mathrm{Frob}(\delta(\mathrm{Frob}\,v)) = v$), and strict of the second kind (`IsStrictSnd`) when $\mathrm{reduceFst}\,W = \mathrm{Frob}(\mathrm{reduceSnd}\,W)$ and $\mathrm{reduceSnd}\,W$ is not fixed.
--
--   The structural hypotheses on these data are: `hTD`, the type dichotomy, that every place $W$ of $F_M$ satisfies $\mathrm{reduceFst}\,W = \mathrm{Frob}(\mathrm{reduceSnd}\,W)$ or $\delta(\mathrm{Frob}(\mathrm{reduceFst}\,W)) = \mathrm{reduceSnd}\,W$; `hmodel`, that $R$ is a model, i.e. the conjunction of the two divisor laws (for a function $f$ integral with nonzero residue on both sides, the pushforward along $\mathrm{reduceFst}$ of the part of $\mathrm{div}(f)$ supported on strict first-kind places computes the order of the $R_1$-residue at every non-fixed place, and symmetrically on the second side) and of the two cusp laws at the infinity side and at the zero side; `hO`, the order law at fixed affine places, expressing the pushforward of $\mathrm{div}(f)$ at such a place $v$ as the sum of the order of the $R_1$-residue at $v$ and of the order of the $R_2$-residue at $\delta(\mathrm{Frob}\,v)$; `hRL`, the regularity law (two clauses: nonnegativity of the residue orders at fixed affine places, and existence of a common value of the two residues at each pair in $SS$, both under the assumption that $f$ has nonnegative order at all places above the place in question); and `hNV`, the node value law, giving at each pair $s \in SS$ not met by the divisor of $f$ a common nonzero value $c \in \kappa$ of the $R_1$-residue at $s_1$ and of the $R_2$-residue at $s_2$.
--
--   The compatibility hypotheses are: `hα_coe`, that $\alpha$ is the identity on underlying Laurent series; `hβ_coe`, that $\beta$ acts on underlying Laurent series by the substitution `qExpand` of index $p$; `hθgal`, that $\theta$ commutes with the action of every $\sigma \in \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ through `arithmeticGalois` on coefficients; and `hβθ`, that $\beta$ equals $\alpha$ followed by $\theta$.
--
--   The two local hypotheses `hLFst` and `hLSnd` are pole bounds of annulus type, stated symmetrically for the two kinds. `hLFst` requires: whenever $Q \neq Q'$ are places of $F_M$, both strict of the first kind, with $\mathrm{reduceFst}\,Q' = \mathrm{reduceFst}\,Q$ and with this common reduction an affine place in the sense of `IsAffinePlace` (some element of $\bar F$ with Laurent expansion `jqModC κ` takes a finite value there), and whenever $n$ is a natural number nonzero in $\kappa$ and $g \in R_1.\mathrm{integers}$ has nonzero $R_1$-residue, $Q.\mathrm{ord}\,g = -n$, $Q'.\mathrm{ord}\,g = n$ and every further strict first-kind place with the same reduction has $\mathrm{ord}\,g = 0$, then for all $e \in A$ and all $\varepsilon \in R_1.\mathrm{integers}$ with nonzero $R_1$-residue such that $g = 1 + e\,\varepsilon$, one has $-1 \le (\mathrm{reduceFst}\,Q).\mathrm{ord}$ of the $R_1$-residue of $\varepsilon$. The hypothesis `hLSnd` is the same with `IsStrictSnd`, $\mathrm{reduceSnd}\,\beta\,\delta$ and $R_2$ in place of `IsStrictFst`, $\mathrm{reduceFst}\,\alpha$ and $R_1$.
--
--   Finally `hUnit` postulates modular units on both sides: there are $u_1, u_2 \in F_M$ and divisors $D_1, D_2$ on $F_M$ with $D_1(W) = W.\mathrm{ord}\,u_1$ and $D_2(W) = W.\mathrm{ord}\,u_2$ for all $W$, such that (i) $u_1$ and $u_1^{-1}$ lie in $R_1.\mathrm{integers}$, the $R_1$-residue of $u_1$ is nonzero, the pushforward along $\mathrm{reduceFst}$ of the strict first-kind part of $D_1$ computes at every non-fixed place $v$ the order at $v$ of that residue, and the pushforward along $\mathrm{reduceFst}$ of the part of $D_1$ supported on infinity-side places computes, at the reduction of each infinity-side place $C$, the order there of that residue; (ii) every nonzero $f \in F_M$ admits $m \neq 0$ and $j \in \mathbb{Z}$ with $f^m u_1^{\,j} \in R_2.\mathrm{integers}$ of nonzero $R_2$-residue; (iii) the mirror statement to (i) for $u_2$, $R_2$, the strict second-kind part of $D_2$, $\mathrm{reduceSnd}\,\beta\,\delta$ and the zero-side places; and (iv) the mirror statement to (ii), every nonzero $f$ admitting $m \neq 0$ and $j \in \mathbb{Z}$ with $f^m u_2^{\,j} \in R_1.\mathrm{integers}$ of nonzero $R_1$-residue.
--
--   Under these hypotheses the conclusion asserts the existence of a finite set $\mathrm{Bad}$ of places of $\bar F$ over $\kappa$ such that every place $v \notin \mathrm{Bad}$ satisfies both of the following. First, there is a place $W$ of $F_M$ over $\overline{\mathbb{Q}}$ which is strict of the first kind for $P, \alpha, \beta, \delta$, has $\mathrm{reduceFst}\,\alpha\,W = v$, and is fixed by the `arithmeticGalois` action of every $\sigma$ in `A.inertiaSubgroupIn ℚ`, the image in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of $A$. Second, there is a place $W$ of $F_M$ which is strict of the second kind, has $\mathrm{reduceSnd}\,\beta\,\delta\,W = v$, and is likewise fixed by the action of every element of `A.inertiaSubgroupIn ℚ`.
--
--   This is the place-lifting step for the two components of the special fibre of $X_H(M)$ at a prime $p$ exactly dividing $M$: away from a finite set of bad reductions, each place of the fibre function field is the prescribed reduction of an inertia-fixed place of the characteristic-zero function field, of the first kind and of the second kind respectively. It is used by [`ModularCurve.JHPlaceSpecialization.exists_inertiaFixed_isStrict_gluedMk_glueData_eq_of_annulus`](thm.html#ModularCurve.JHPlaceSpecialization.exists_inertiaFixed_isStrict_gluedMk_glueData_eq_of_annulus) to produce inertia-fixed points with prescribed image in the glued model of the fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHPlaceSpecialization_exists_finset_forall_exists_isStrictFst_reduceFst_eq_and_isStrictSnd_reduceSnd_eq_forall_inertia_smul_eq_of_gammaLift.lean

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_AlgebraicCurve_AdelicIndex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open scoped MatrixGroups Classical

theorem ModularCurve.JHPlaceSpecialization.exists_finset_forall_exists_isStrictFst_reduceFst_eq_and_isStrictSnd_reduceSnd_eq_forall_inertia_smul_eq_of_gammaLift
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (α β : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : β.IsIntegral)

    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v)

    (SS : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (hSS : ∀ s, s ∈ SS ↔ s ∈ ssNodePairsQExp (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p)

    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)
    (hTD : Psp.TypeDichotomy α β hα hβ δ)
    (hmodel : Rpd.IsModel α β hα hβ δ) (hO : Rpd.OrderLawFixed α β hα hβ δ)
    (hRL : Rpd.RegularityLaw α β hα hβ δ SS) (hNV : Rpd.NodeValueLaw α β hα hβ δ SS)

    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hβ_coe : ∀ u, ((β u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hθgal : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (f : ↥(xHFunctionFieldBar M H)),
      θ (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • f) = arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • θ f)
    (hβθ : β = (θ : ↥(xHFunctionFieldBar M H) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H)).comp α)

    (hLFst : ∀ (Q Q' : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), Psp.IsStrictFst α β hα hβ δ Q → Psp.IsStrictFst α β hα hβ δ Q' →
      Psp.reduceFst α hα Q' = Psp.reduceFst α hα Q → Q' ≠ Q → JHPlaceSpecialization.IsAffinePlace p M H hpM A (Psp.reduceFst α hα Q) →
      ∀ (n : ℕ), (n : (ResidueField ↥A)) ≠ 0 → ∀ (g : ↥(xHFunctionFieldBar M H)) (hg₁ : g ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨g, hg₁⟩ ≠ 0 →
      Q.ord g = -(n : ℤ) → Q'.ord g = n →
      (∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.IsStrictFst α β hα hβ δ W → Psp.reduceFst α hα W = Psp.reduceFst α hα Q → W ≠ Q → W ≠ Q' → W.ord g = 0) →
      ∀ (e : ↥A) (ε : ↥(xHFunctionFieldBar M H)) (hε₁ : ε ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨ε, hε₁⟩ ≠ 0 →
      g = 1 + algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (e : AlgebraicClosure ℚ) * ε →
      -1 ≤ (Psp.reduceFst α hα Q).ord (Rpd.R₁.residue ⟨ε, hε₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (hLSnd : ∀ (Q Q' : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), Psp.IsStrictSnd α β hα hβ δ Q → Psp.IsStrictSnd α β hα hβ δ Q' →
      Psp.reduceSnd β hβ δ Q' = Psp.reduceSnd β hβ δ Q → Q' ≠ Q → JHPlaceSpecialization.IsAffinePlace p M H hpM A (Psp.reduceSnd β hβ δ Q) →
      ∀ (n : ℕ), (n : (ResidueField ↥A)) ≠ 0 → ∀ (g : ↥(xHFunctionFieldBar M H)) (hg₂ : g ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨g, hg₂⟩ ≠ 0 →
      Q.ord g = -(n : ℤ) → Q'.ord g = n →
      (∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.IsStrictSnd α β hα hβ δ W → Psp.reduceSnd β hβ δ W = Psp.reduceSnd β hβ δ Q → W ≠ Q → W ≠ Q' → W.ord g = 0) →
      ∀ (e : ↥A) (ε : ↥(xHFunctionFieldBar M H)) (hε₂ : ε ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨ε, hε₂⟩ ≠ 0 →
      g = 1 + algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (e : AlgebraicClosure ℚ) * ε →
      -1 ≤ (Psp.reduceSnd β hβ δ Q).ord (Rpd.R₂.residue ⟨ε, hε₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))

    (hUnit : ∃ (u₁ u₂ : ↥(xHFunctionFieldBar M H)) (D₁ D₂ : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)),
      (∀ W, D₁ W = W.ord u₁) ∧ (∀ W, D₂ W = W.ord u₂) ∧

      (∃ h₁ : u₁ ∈ Rpd.R₁.integers, Rpd.R₁.residue ⟨u₁, h₁⟩ ≠ 0 ∧ u₁⁻¹ ∈ Rpd.R₁.integers ∧
        (∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), ¬ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v →
          Finsupp.mapDomain (Psp.reduceFst α hα) (Psp.fstDiv α β hα hβ δ D₁) v = v.ord (Rpd.R₁.residue ⟨u₁, h₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))) ∧
        (∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A) C →
          Finsupp.mapDomain (Psp.reduceFst α hα) (D₁.filter (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A))) (Psp.reduceFst α hα C) =
            (Psp.reduceFst α hα C).ord (Rpd.R₁.residue ⟨u₁, h₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))) ∧
      (∀ f : ↥(xHFunctionFieldBar M H), f ≠ 0 → ∃ (m : ℕ) (j : ℤ), m ≠ 0 ∧
        ∃ h₂ : f ^ m * u₁ ^ j ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨f ^ m * u₁ ^ j, h₂⟩ ≠ 0) ∧

      (∃ h₂ : u₂ ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨u₂, h₂⟩ ≠ 0 ∧ u₂⁻¹ ∈ Rpd.R₂.integers ∧
        (∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), ¬ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v →
          Finsupp.mapDomain (Psp.reduceSnd β hβ δ) (Psp.sndDiv α β hα hβ δ D₂) v = v.ord (Rpd.R₂.residue ⟨u₂, h₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))) ∧
        (∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A) C →
          Finsupp.mapDomain (Psp.reduceSnd β hβ δ) (D₂.filter (JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A))) (Psp.reduceSnd β hβ δ C) =
            (Psp.reduceSnd β hβ δ C).ord (Rpd.R₂.residue ⟨u₂, h₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))) ∧
      (∀ f : ↥(xHFunctionFieldBar M H), f ≠ 0 → ∃ (m : ℕ) (j : ℤ), m ≠ 0 ∧
        ∃ h₁ : f ^ m * u₂ ^ j ∈ Rpd.R₁.integers, Rpd.R₁.residue ⟨f ^ m * u₂ ^ j, h₁⟩ ≠ 0))
    :
    ∃ Bad : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))),
      ∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), v ∉ Bad →
        (∃ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
          Psp.IsStrictFst α β hα hβ δ W ∧ Psp.reduceFst α hα W = v ∧
            ∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • W = W) ∧
        (∃ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
          Psp.IsStrictSnd α β hα hβ δ W ∧ Psp.reduceSnd β hβ δ W = v ∧
            ∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • W = W) := by sorry
