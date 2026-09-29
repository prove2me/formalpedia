-- Prove2me | Theorems.Thm_ModularCurve_JHPlaceSpecialization_exists_annulusPositionLaw_inertiaInvariant_exists_fixed_of_annulus
-- name    : ModularCurve.JHPlaceSpecialization.exists_annulusPositionLaw_inertiaInvariant_exists_fixed_of_annulus
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/eaf86ba2-9d2f-5dd6-a023-d16a94a8aeae
-- title:
--   Inertia-invariant rational positions on the supersingular annuli
-- statement:
--   Throughout, $p$ is a prime and $M$ a nonzero natural number with $p \mid M$ and $p^2 \nmid M$, and $H$ is a subgroup of $(\mathbf{Z}/M)^\times$ containing every unit that reduces to $1$ in $(\mathbf{Z}/(M/p))^\times$ (hypothesis `hHp`). Further, $A$ is a valuation subring of $\overline{\mathbf{Q}}$ with $p$ a nonunit of $A$ (`hA : A.LiesOverPrime p`), whose residue field $\kappa =$ `ResidueField ↥A` is of characteristic $p$ and algebraically closed. Write $F_M =$ `xHFunctionFieldBar M H` for the base change to $\overline{\mathbf{Q}}$ of the $q$-expansion function field of $X_H(M)$ inside Laurent series, $F_{M/p} =$ `xHFunctionFieldBar (M/p) (infSubgroup p M H hpM)` for the corresponding field at level $M/p$ with the image subgroup `infSubgroup p M H hpM`, and $\bar F =$ `Fbar p M H hpM κ` $=$ `qExpFunctionFieldC κ (ΓN p M H hpM)` for the characteristic-$p$ function field at the geometric level.
--
--   The degeneracy data consist of: an $\overline{\mathbf{Q}}$-algebra automorphism $\theta$ of $F_M$; an $\overline{\mathbf{Q}}$-algebra map $\alpha : F_{M/p} \to F_M$ with $\alpha$ integral (`hα`) and $\alpha$ followed by $\theta$ integral (`hβ`); the hypothesis `hα_coe` that $\alpha$ is the identity on Laurent series, and `hβ_coe` that $\theta \circ \alpha$ acts on Laurent series by `qExpand` at $p$, i.e. by $q \mapsto q^p$. A unit $pb$ of $\mathbf{Z}/(M/p)$ is given whose underlying element is $p$ (`hpb`), and $\delta$ is a self-map of the set of places of $\bar F$ over $\kappa$ which, by `hδ`, is the action on places of the semilinear automorphism `SemilinearAut.ofAlgAut` attached to the diamond automorphism `diamondActionModL κ (M/p) (infSubgroup p M H hpM)` evaluated at [`CuspForm.gammaLift (M/p) pb`](def/CuspForm_HeckeOperatorFormsGammaH.html#L36). Finally `SS` is a finite set of pairs of places of $\bar F$ which, by `hSS`, is exactly `ssNodePairsQExp κ (ΓN p M H hpM) p`: the pairs $s$ whose second component is a supersingular place and whose first component is its $q$-expansion Frobenius image `qExpFrobeniusPlaceModL`.
--
--   The specialisation datum `Psp : JHPlaceSpecialization p M H hpM A` provides a surjective map `sp` from places of $F_{M/p}$ to places of $\bar F$, a homomorphism on degree-zero divisor class groups, and the compatibility clauses of that structure ($q$-expansion compatibility of orders, divisor lifting, invariance under inertia, transformation into `qExpFrobeniusPlaceModL` under a Frobenius element, and compatibility with the class-group map). From it are formed `Psp.reduceFst α hα` (restrict a place of $F_M$ along $\alpha$, then apply `sp`) and `Psp.reduceSnd (θ ∘ α) hβ δ` (restrict along $\theta \circ \alpha$, apply `sp`, then $\delta$), and the predicates `IsStrictFst` ($\delta(\mathrm{Frob}(\mathrm{red}_1 W)) = \mathrm{red}_2 W$ and $\mathrm{red}_1 W$ is not `Fixed` for $\delta$) and `IsStrictSnd` ($\mathrm{red}_1 W = \mathrm{Frob}(\mathrm{red}_2 W)$ and $\mathrm{red}_2 W$ is not `Fixed`), where a place $v$ is `Fixed` when $\mathrm{Frob}(\delta(\mathrm{Frob}(v))) = v$. The prolongation datum `Rpd : Psp.ProlongationDatum θ` consists of two regular prolongations $R_1, R_2$ of $A$ to $F_M$ with residue field $\bar F$, together with the $q$-expansion compatibility of the residue map of $R_1$ and the relations $f \in R_2.\mathrm{integers} \iff \theta f \in R_1.\mathrm{integers}$ and $R_2.\mathrm{residue}(f) = R_1.\mathrm{residue}(\theta f)$.
--
--   The hypotheses on this kit are: `hFix`, that every supersingular place $y$ of $\bar F$ and its Frobenius image `qExpFrobeniusPlaceModL … y` are `Fixed` for $\delta$; `hTD`, the type dichotomy asserting that each place $W$ of $F_M$ satisfies $\mathrm{red}_1 W = \mathrm{Frob}(\mathrm{red}_2 W)$ or $\delta(\mathrm{Frob}(\mathrm{red}_1 W)) = \mathrm{red}_2 W$; `hmodel`, the conjunction of the four laws `Rpd.DivisorLawFst`, `Rpd.DivisorLawSnd`, `Rpd.CuspLawInfty`, `Rpd.CuspLawZero`; `hO`, the order law at fixed affine places, which says that for $f$ lying in both rings of integers with both residues nonzero and $D$ the divisor of $f$, the pushforward of $D$ along $\mathrm{red}_1$ at a `Fixed` place $v$ which is an `IsAffinePlace` equals $\mathrm{ord}_v(R_1.\mathrm{residue}\,f) + \mathrm{ord}_{\delta(\mathrm{Frob}\,v)}(R_2.\mathrm{residue}\,f)$; `hreg`, the regularity law in two clauses (transfer of nonnegativity of orders to the two residues at fixed affine places, and the existence of a common value of the two residues at each node pair in `SS`); and `hnv`, the node value law, which produces a nonzero $c \in \kappa$ with $s_1$ taking value $c$ on $R_1.\mathrm{residue}\,f$ and $s_2$ taking value $c$ on $R_2.\mathrm{residue}\,f$, for $s \in$ `SS` over whose pair no place in the support of the divisor of $f$ lies.
--
--   The Galois hypotheses are `hθgal`, that $\theta$ commutes with the semilinear action `arithmeticGalois` of $\sigma \in \mathrm{Gal}(\overline{\mathbf{Q}}/\mathbf{Q})$ on $F_M$, and `hFixFin`, that the set of $\delta$-`Fixed` places of $\bar F$ is finite.
--
--   Two residue pole bounds are assumed, `hLFst` and `hLSnd`, one for each side. In `hLFst`: for places $Q \neq Q'$ of $F_M$ that are both `IsStrictFst` with the same image under $\mathrm{red}_1$, that image being an `IsAffinePlace`; for every natural $n$ nonzero in $\kappa$; for every $g \in R_1.\mathrm{integers}$ with nonzero $R_1$-residue such that $\mathrm{ord}_Q g = -n$, $\mathrm{ord}_{Q'} g = n$ and $\mathrm{ord}_W g = 0$ for every other `IsStrictFst` place $W$ with the same $\mathrm{red}_1$-image; and for every $e \in A$ and $\varepsilon \in R_1.\mathrm{integers}$ with nonzero $R_1$-residue such that $g = 1 + e\varepsilon$: then $-1 \le \mathrm{ord}_{\mathrm{red}_1 Q}(R_1.\mathrm{residue}\,\varepsilon)$. The hypothesis `hLSnd` is the same statement with `IsStrictSnd`, $\mathrm{red}_2$ and $R_2$ in place of `IsStrictFst`, $\mathrm{red}_1$ and $R_1$.
--
--   The hypothesis `hUnit` asserts the existence of $u_1, u_2 \in F_M$ and divisors $D_1, D_2$ on $F_M$ with $D_i(W) = \mathrm{ord}_W u_i$ for all $W$, such that: $u_1$ and $u_1^{-1}$ lie in $R_1.\mathrm{integers}$ with nonzero $R_1$-residue, the pushforward along $\mathrm{red}_1$ of the strict-first part `Psp.fstDiv … D₁` agrees at every non-`Fixed` place $v$ with $\mathrm{ord}_v(R_1.\mathrm{residue}\,u_1)$, and the pushforward along $\mathrm{red}_1$ of the restriction of $D_1$ to the `IsInftySide` places agrees, at $\mathrm{red}_1 C$ for each `IsInftySide` place $C$, with $\mathrm{ord}_{\mathrm{red}_1 C}(R_1.\mathrm{residue}\,u_1)$; moreover every nonzero $f \in F_M$ admits $m \neq 0$ and $j \in \mathbf{Z}$ with $f^m u_1^{\,j} \in R_2.\mathrm{integers}$ of nonzero $R_2$-residue. Symmetrically $u_2$ and $u_2^{-1}$ lie in $R_2.\mathrm{integers}$ with nonzero $R_2$-residue, with the analogous two identities for `Psp.sndDiv … D₂` and for the restriction of $D_2$ to the `IsZeroSide` places, both pushed forward along $\mathrm{red}_2$, and every nonzero $f$ admits $m \neq 0$, $j \in \mathbf{Z}$ with $f^m u_2^{\,j} \in R_1.\mathrm{integers}$ of nonzero $R_1$-residue.
--
--   The cusp and orientation hypotheses are: `hcusp`, that every place $w$ of $\bar F$ which is not an `IsAffinePlace` is both $\mathrm{red}_1 C$ for some `IsInftySide` place $C$ and $\mathrm{red}_2 C$ for some `IsZeroSide` place $C$; `horientInf`, that $\delta(\mathrm{Frob}(\mathrm{red}_1 C)) = \mathrm{red}_2 C$ for every `IsInftySide` place $C$; and `horient0`, that $\mathrm{red}_1 C = \mathrm{Frob}(\mathrm{red}_2 C)$ for every `IsZeroSide` place $C$.
--
--   Finally, a depth function $e :$ `SS` $\to \mathbf{N}$ is given with $0 < e(s)$ for all $s$ (`he`), together with a family of annuli $An(s)$ of $F_M$ over $A$ (objects of [`AlgebraicCurve.Annulus A F_M`](def/AlgebraicCurve_SemistableCharts.html#L86): a domain of places, a parameter, a modulus in the maximal ideal of $A$, with the rationality, uniqueness, order and unit clauses of that structure). The hypothesis `hAn` requires, for each $s \in$ `SS`, that: a place $W$ lies in $An(s).\mathrm{dom}$ exactly when $\mathrm{red}_1 W = s_1$ and $W$ is neither `IsStrictFst` nor `IsStrictSnd`; $An(s).\mathrm{modulus} = p^{e(s)}u$ for some unit $u$ of $A$; the parameter is fixed by `arithmeticGalois σ` for every $\sigma$ in the inertia subgroup `A.inertiaSubgroupIn ℚ`; the quotient $(\text{modulus})^{-1}\cdot \mathrm{param}$ lies in $R_1.\mathrm{integers}$; the parameter lies in $R_2.\mathrm{integers}$ with nonzero $R_2$-residue; $\mathrm{ord}_{s_2}(R_2.\mathrm{residue}(\mathrm{param})) = 1$ and, for every $f \in R_2.\mathrm{integers}$ of nonzero residue with $\mathrm{ord}_P f = 0$ for all $P$ in the domain, the element $P(f)\cdot P(\mathrm{param})^{-\mathrm{ord}_{s_2}(R_2.\mathrm{residue}\,f)}$ lies in $A$ and is a unit there, for every $P$ in the domain (values taken with `Place.evalAt`); and symmetrically $(\text{modulus})\cdot \mathrm{param}^{-1} \in R_1.\mathrm{integers}$ with $\mathrm{ord}_{s_1}$ of its $R_1$-residue equal to $1$, and the same unit statement with $R_1$, $s_1$ and the flipped parameter $(\text{modulus})\cdot\mathrm{param}^{-1}$. The hypothesis `hAnn` asserts, for each $s \in$ `SS`, the existence of an annulus satisfying precisely this list of clauses.
--
--   Under these hypotheses there exists a function $\mathrm{pos} :$ `SS` $\to$ (places of $F_M$) $\to \mathbf{Q}$ with the following three properties.
--
--   First, `JHPlaceSpecialization.AnnulusPositionLaw SS e An pos` holds: for every $s$ and every place $V \in An(s).\mathrm{dom}$ one has $0 < \mathrm{pos}\,s\,V$ and $\mathrm{pos}\,s\,V < e(s)$, and
--   $$A.\mathrm{valuation}\Bigl(V\bigl((\text{modulus}_s)\cdot \mathrm{param}_s^{-1}\bigr)\Bigr)^{\mathrm{den}(\mathrm{pos}\,s\,V)} = A.\mathrm{valuation}(p)^{\mathrm{num}(\mathrm{pos}\,s\,V)},$$
--   the value of the flipped parameter at $V$ being taken with `Place.evalAt`, the exponent on the left the denominator of the rational number $\mathrm{pos}\,s\,V$ and that on the right its numerator as a natural number.
--
--   Second, each $\mathrm{pos}\,s$ is invariant under inertia: $\mathrm{pos}\,s\,(\mathrm{arithmeticGalois}\,\sigma \cdot V) = \mathrm{pos}\,s\,V$ for every $\sigma \in$ `A.inertiaSubgroupIn ℚ` and every place $V$ of $F_M$.
--
--   Third, for every $s$ and every natural number $d$ with $0 < d < e(s)$ there is a place $V \in An(s).\mathrm{dom}$ which is itself fixed by inertia, that is `arithmeticGalois` $\sigma \cdot V = V$ for all $\sigma \in$ `A.inertiaSubgroupIn ℚ`, and which satisfies $\mathrm{pos}\,s\,V = d$.
--
--   This is the statement that the annuli of the semistable model of $X_H(M)$ at a prime $p$ dividing $M$ exactly once carry a rational position (depth) function, read on the flipped parameter $\text{modulus}/\text{param}$ and hence measured from the first component, which is inertia-invariant and attains every integer position strictly between $0$ and the depth $e(s)$ at an inertia-fixed place. It is used in the construction of inertia-fixed representatives of inertia-invariant divisor classes and in the accompanying computation with the component group of the Jacobian at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHPlaceSpecialization_exists_annulusPositionLaw_inertiaInvariant_exists_fixed_of_annulus.lean

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

theorem ModularCurve.JHPlaceSpecialization.exists_annulusPositionLaw_inertiaInvariant_exists_fixed_of_annulus
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
              (-(s.1.1.ord (Rpd.R₁.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A))) :
    ∃ pos : ↥SS → Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) → ℚ,
      JHPlaceSpecialization.AnnulusPositionLaw SS e An pos ∧
      (∀ (s : ↥SS), ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
        pos s ((arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • V) = pos s V) ∧
      (∀ (s : ↥SS) (d : ℕ), 0 < d → d < e s → ∃ V ∈ (An s).dom,
        (∀ σ ∈ A.inertiaSubgroupIn ℚ, (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • V = V) ∧ pos s V = d) := by sorry
