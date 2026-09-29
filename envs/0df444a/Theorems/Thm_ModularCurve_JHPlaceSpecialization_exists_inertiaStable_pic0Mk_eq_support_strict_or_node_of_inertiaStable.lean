-- Prove2me | Theorems.Thm_ModularCurve_JHPlaceSpecialization_exists_inertiaStable_pic0Mk_eq_support_strict_or_node_of_inertiaStable
-- name    : ModularCurve.JHPlaceSpecialization.exists_inertiaStable_pic0Mk_eq_support_strict_or_node_of_inertiaStable
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/97f78863-7ff8-5e8a-93c3-439b141015e7
-- title:
--   Inertia-stable representatives with strict or nodal support
-- statement:
--   Throughout, $p$ is a prime and $M$ a nonzero natural number with $p \mid M$ and $p^2 \nmid M$, and $H$ is a subgroup of $(\mathbb{Z}/M)^\times$ containing the kernel of the reduction $(\mathbb{Z}/M)^\times \to (\mathbb{Z}/(M/p))^\times$ (the hypothesis `hHp`: every unit $u$ with `ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1` lies in $H$). Further, $A$ is a valuation subring of $\overline{\mathbb{Q}}$ lying over $p$ in the sense that $p$ is a nonunit of $A$ (`hA : A.LiesOverPrime p`), and its residue field $\kappa =$ `ResidueField A` is of characteristic $p$ and algebraically closed.
--
--   Write $F_M$ for `xHFunctionFieldBar M H`, the base change to $\overline{\mathbb{Q}}$ of the function field of $X_H(M)$ inside $\overline{\mathbb{Q}}$-Laurent series, $F_{M/p}$ for `xHFunctionFieldBar (M/p) (infSubgroup p M H hpM)`, where `infSubgroup p M H hpM` is the image of $H$ in $(\mathbb{Z}/(M/p))^\times$, and $\mathcal{F}$ for `Fbar p M H hpM κ`, the $q$-expansion function field `qExpFunctionFieldC κ (ΓN p M H hpM)` over $\kappa$. The data are: a $\overline{\mathbb{Q}}$-algebra automorphism $\theta$ of $F_M$; a $\overline{\mathbb{Q}}$-algebra map $\alpha : F_{M/p} \to F_M$, with $\beta$ denoting the composite $\theta \circ \alpha$ (`θ.toAlgHom.comp α`); hypotheses `hα`, `hβ` that $\alpha$ and $\beta$ are integral; the normalisations `hα_coe`, that $\alpha$ is the identity on Laurent expansions, and `hβ_coe`, that the Laurent expansion of $\beta u$ is `qExpand _ p` applied to that of $u$ (substitution $q \mapsto q^p$); a unit $pb$ of $\mathbb{Z}/(M/p)$ reducing to $p$ (`hpb`); a self-map $\delta$ of the places of $\mathcal{F}$ over $\kappa$ which, by `hδ`, is the action on places of the semilinear automorphism attached to `diamondActionModL κ (M/p) (infSubgroup p M H hpM)` evaluated at a $\Gamma_0(M/p)$-lift [`CuspForm.gammaLift (M/p) pb`](def/CuspForm_HeckeOperatorFormsGammaH.html#L36) of $pb$, i.e. the reduced diamond operator $\langle p \rangle$; and a finite set $SS$ of pairs of places of $\mathcal{F}$ which, by `hSS`, consists exactly of the pairs in `ssNodePairsQExp κ (ΓN p M H hpM) p`, that is the pairs $s$ whose second entry is a supersingular place and whose first entry is $\Phi(s_2)$, where $\Phi =$ `qExpFrobeniusPlaceModL κ (ΓN p M H hpM) p` is restriction of places along the mod-$p$ Frobenius. Finally, `Psp` is a place-specialisation datum `JHPlaceSpecialization p M H hpM A` (a map `sp` from places of $F_{M/p}$ to places of $\mathcal{F}$ together with a map on $\mathrm{Pic}^0$ and the compatibilities `d0_qexp`, surjectivity `d4`, `d5`, inertia and Frobenius equivariance `d6_inertia`, `d6_frobenius`, and `spPic0_compat`), and `Rpd` is a prolongation datum `ProlongationDatum Psp θ`, consisting of two regular prolongations $R_1, R_2$ of $A$ to $F_M$ with residue fields mapping to $\mathcal{F}$, linked by $\theta$ via `mem_integers₂_iff` and `residue₂_eq`. Notation: $\pi_1 W =$ `Psp.reduceFst α hα W` $=$ `Psp.sp (W.restrictAlong α hα)` and $\pi_2 W =$ `Psp.reduceSnd β hβ δ W` $= \delta(\mathrm{sp}(W|_\beta))$; a place $v$ of $\mathcal{F}$ is $\delta$-fixed when $\Phi(\delta(\Phi v)) = v$, and affine when the series `jqModC κ` is realised by an element of $\mathcal{F}$ having a value at $v$; a place $W$ of $F_M$ is strict of the first kind when $\delta(\Phi(\pi_1 W)) = \pi_2 W$ and $\pi_1 W$ is not $\delta$-fixed, and strict of the second kind when $\pi_1 W = \Phi(\pi_2 W)$ and $\pi_2 W$ is not $\delta$-fixed.
--
--   The hypotheses fall into the following groups. Fixing laws: `hFix`, that every supersingular place $y$ in `ssPlacesQExp κ (ΓN p M H hpM) p` and its Frobenius $\Phi y$ are $\delta$-fixed. Dichotomy: `hTD`, that every place $W$ of $F_M$ satisfies $\pi_1 W = \Phi(\pi_2 W)$ or $\delta(\Phi(\pi_1 W)) = \pi_2 W$. Model laws: `hmodel`, the conjunction of `DivisorLawFst`, `DivisorLawSnd`, `CuspLawInfty` and `CuspLawZero` for `Rpd`. Order law `hO`: for $f \in F_M$ lying in the integers of both prolongations with nonzero residues, and $D$ the divisor of $f$, at every $\delta$-fixed affine place $v$ the push-forward $(\pi_1)_*D$ takes at $v$ the value $\mathrm{ord}_v(R_1\text{-residue of } f) + \mathrm{ord}_{\delta(\Phi v)}(R_2\text{-residue of } f)$. Regularity law `hreg` (two clauses, relative to $SS$): positivity of the residues' orders at $\delta$-fixed affine places when $f$ has nonnegative order on the relevant fibre, and, for $s \in SS$, existence of a common value $c \in \kappa$ of the two residues at $s_1$ and $s_2$. Node-value law `hnv`: for such $f$ and $s \in SS$, if no place $V$ with $\mathrm{ord}_V f \neq 0$ satisfies $\pi_1 V = s_1$ and $\pi_2 V = s_2$, then the two residues take a common nonzero value $c$ at $s_1$ and $s_2$. Galois compatibility `hθgal`: $\theta$ commutes with the arithmetic Galois action `arithmeticGalois (xHFunctionField M H) σ` for all $\sigma \in \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$. Finiteness `hFixFin`: the set of $\delta$-fixed places of $\mathcal{F}$ is finite.
--
--   Two local laws `hLFst` and `hLSnd`, mirror images of each other, are imposed. In `hLFst`: for places $Q \neq Q'$ of $F_M$, both strict of the first kind, with $\pi_1 Q' = \pi_1 Q$ an affine place, for every $n \in \mathbb{N}$ nonzero in $\kappa$, every $g$ in the integers of $R_1$ with nonzero residue such that $\mathrm{ord}_Q g = -n$, $\mathrm{ord}_{Q'} g = n$ and $\mathrm{ord}_W g = 0$ for every other strict-first place $W$ with $\pi_1 W = \pi_1 Q$, and for all $e \in A$ and $\varepsilon$ in the integers of $R_1$ with nonzero residue such that $g = 1 + e\varepsilon$, one has $-1 \le \mathrm{ord}_{\pi_1 Q}(R_1\text{-residue of } \varepsilon)$. The hypothesis `hLSnd` is the same with $\pi_2$, $R_2$ and strictness of the second kind.
--
--   The modular-unit hypothesis `hUnit` asserts the existence of $u_1, u_2 \in F_M$ and divisors $D_1, D_2$ with $D_i(W) = \mathrm{ord}_W u_i$ for all $W$, such that: $u_1$ and $u_1^{-1}$ lie in the integers of $R_1$, the $R_1$-residue of $u_1$ is nonzero, for every place $v$ of $\mathcal{F}$ that is not $\delta$-fixed the push-forward under $\pi_1$ of the strict-first part of $D_1$ takes at $v$ the value $\mathrm{ord}_v$ of that residue, and for every $\infty$-side place $C$ of $F_M$ (i.e. $C$ cuspidal in the sense of `IsCuspidal`, with elements of $F_M$ expanding to `jqModC` and to `qExpand _ p jqModC` whose ratio $x'/x^p$ has at $C$ a value $\tau \in A$ of residue $1$) the push-forward under $\pi_1$ of the $\infty$-side part of $D_1$ takes at $\pi_1 C$ the same order; that for every nonzero $f \in F_M$ there are $m \neq 0$ and $j \in \mathbb{Z}$ with $f^m u_1^{\,j}$ in the integers of $R_2$ with nonzero residue; and the mirror statements for $u_2$, $D_2$, $R_2$, $\pi_2$, the strict-second part of $D_2$ and the $0$-side places (defined by `IsCuspidal'` and a value $\tau$ of residue $1$ for $x/x'^p$), together with: for every nonzero $f$ there are $m \neq 0$ and $j$ with $f^m u_2^{\,j}$ in the integers of $R_1$ with nonzero residue.
--
--   The cusp-cover hypothesis `hcusp` requires every non-affine place $w$ of $\mathcal{F}$ to be of the form $\pi_1 C$ for some $\infty$-side place $C$ and also of the form $\pi_2 C'$ for some $0$-side place $C'$. The orientation hypotheses are `horientInf`, that $\delta(\Phi(\pi_1 C)) = \pi_2 C$ for every $\infty$-side place $C$, and `horient0`, that $\pi_1 C = \Phi(\pi_2 C)$ for every $0$-side place $C$.
--
--   Finally, the annulus block: a function $e : SS \to \mathbb{N}$ with $e(s) > 0$ for all $s$ (`he`), and `hAnn`, which for each $s \in SS$ provides an annulus `An : AlgebraicCurve.Annulus A F_M` (a set `dom` of places, a parameter `param`, and a modulus in the maximal ideal of $A$, subject to the rationality, evaluation, uniqueness, $\mathrm{ord}(\mathrm{param} - \text{value}) = 1$ and unit-principle axioms of that structure) such that: `An.dom` consists exactly of the places $W$ with $\pi_1 W = s_1$ that are strict of neither kind; `An.modulus` is $p^{e(s)}$ times a unit of $A$; `An.param` is invariant under the arithmetic Galois action of every $\sigma$ in the inertia subgroup `A.inertiaSubgroupIn ℚ`; $(\text{modulus})^{-1} \cdot \mathrm{param}$ lies in the integers of $R_1$; `An.param` lies in the integers of $R_2$ with nonzero residue; moreover the $R_2$-residue of `An.param` has order $1$ at $s_2$, and for every $f$ in the integers of $R_2$ with nonzero residue and $\mathrm{ord}_P f = 0$ for all $P \in$ `An.dom`, at every such $P$ the element $P(f) \cdot P(\mathrm{param})^{-\mathrm{ord}_{s_2}(R_2\text{-residue of } f)}$ lies in $A$ and is a unit there; and the matching clause for $R_1$ with the element $(\text{modulus}) \cdot \mathrm{param}^{-1}$, whose $R_1$-residue has order $1$ at $s_1$, and with $P((\text{modulus})\mathrm{param}^{-1})^{-\mathrm{ord}_{s_1}(R_1\text{-residue of } f)}$ in place of the above.
--
--   Under these hypotheses the conclusion is: for every degree-zero divisor $D_0$ of $F_M$ over $\overline{\mathbb{Q}}$ (an element of `Divisor.degZero`) which is fixed by the arithmetic Galois action of every $\sigma \in$ `A.inertiaSubgroupIn ℚ`, there exists a degree-zero divisor $D$ such that
--
--   (i) `Pic0.mk D = Pic0.mk D₀`, i.e. $D$ and $D_0$ have the same class in $\mathrm{Pic}^0$ of $F_M$ over $\overline{\mathbb{Q}}$;
--
--   (ii) $\sigma \cdot D = D$ for every $\sigma \in$ `A.inertiaSubgroupIn ℚ`, for the same arithmetic Galois action;
--
--   (iii) every place $V$ in the support of $D$ is strict of the first kind, or strict of the second kind, or satisfies $\pi_1 V = s_1$ for some pair $s \in SS$.
--
--   This is the moving step in the construction of inertia-stable representatives for inertia-invariant classes in the Jacobian of $X_H(M)$ at a prime $p$ exactly dividing $M$: an inertia-invariant degree-zero divisor is replaced, within its linear equivalence class, by an inertia-invariant divisor whose support meets only the places that are strict for one of the two reductions or reduce to a first coordinate of a supersingular node pair. It feeds the representative theorem for inertia-invariant classes, [`ModularCurve.JHPlaceSpecialization.exists_rep_inertiaFixed_support_strict_or_node_of_mem_inertiaInvariants_of_annulus_of_fixReg`](thm.html#ModularCurve.JHPlaceSpecialization.exists_rep_inertiaFixed_support_strict_or_node_of_mem_inertiaInvariants_of_annulus_of_fixReg).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHPlaceSpecialization_exists_inertiaStable_pic0Mk_eq_support_strict_or_node_of_inertiaStable.lean

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

theorem ModularCurve.JHPlaceSpecialization.exists_inertiaStable_pic0Mk_eq_support_strict_or_node_of_inertiaStable
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
              (-(s.1.1.ord (Rpd.R₁.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A))) :
    ∀ D₀ : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H))),
      (∀ σ ∈ A.inertiaSubgroupIn ℚ, (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • (D₀ : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) = D₀) →
      ∃ D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H))),
        Pic0.mk D = Pic0.mk D₀ ∧
        (∀ σ ∈ A.inertiaSubgroupIn ℚ, (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) = D) ∧
        (∀ V ∈ (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)).support, (Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ V ∨ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ V ∨ ∃ s ∈ SS, Psp.reduceFst α hα V = s.1)) := by sorry
