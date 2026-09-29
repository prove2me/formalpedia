-- Prove2me | Theorems.Thm_ModularCurve_JHPlaceSpecialization_ProlongationDatum_IsModel_residue_mem_riemannRochSpace_mapDomain_and_node_hasValue_of_isGoodDiv
-- name    : ModularCurve.JHPlaceSpecialization.ProlongationDatum.IsModel.residue_mem_riemannRochSpace_mapDomain_and_node_hasValue_of_isGoodDiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/f252062e-9ef6-577b-8cd0-f86828237b97
-- title:
--   Residue boxes and node values for a good divisor
-- statement:
--   Throughout, $p$ is a prime and $M$ a non-zero natural number with $p \mid M$ and $p^2 \nmid M$, $H$ is a subgroup of $(\mathbb Z/M)^\times$ containing every unit whose image under `ZMod.unitsMap` for $M/p \mid M$ is trivial (hypothesis `hHp`), and $M/p$ is non-zero. Further, $A$ is a valuation subring of $\overline{\mathbb Q}$ lying over $p$ in the sense of [`ValuationSubring.LiesOverPrime`](def/FLTPrelim_Ramification.html#L16) (that is, $p$ is a non-unit of $A$), whose residue field $\kappa$ is of characteristic $p$ and algebraically closed. Write $F =$ `xHFunctionFieldBar M H` for the base change to $\overline{\mathbb Q}$ of the $q$-expansion function field of $X_H(M)$, $F' =$ `xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)` for the corresponding field at level $M/p$ with the image subgroup `infSubgroup p M H hpM` of $H$ in $(\mathbb Z/(M/p))^\times$, and $\bar F =$ `JHNeronObjectAtP.Fbar p M H hpM κ`, the characteristic-$p$ $q$-expansion function field at level `ΓN p M H hpM` over $\kappa$.
--
--   The data are: an automorphism $\theta$ of $F$ over $\overline{\mathbb Q}$; an algebra homomorphism $\alpha : F' \to F$ over $\overline{\mathbb Q}$, integral (`hα`), such that $\theta \circ \alpha$ is integral as well (`hβ`); the normalisation `hα_coe`, that $\alpha$ does not change the underlying Laurent series, and `hβ_coe`, that the Laurent series of $(\theta\circ\alpha)(u)$ is `qExpand` at $p$ of that of $u$; a unit $pb$ of $\mathbb Z/(M/p)$ whose underlying residue is $p$; a self-map $\delta$ of the places of $\bar F$ over $\kappa$ which, by `hδ`, is the translation action of the semilinear automorphism attached to the diamond operator `diamondActionModL` at a $\Gamma_0(M/p)$-lift [`CuspForm.gammaLift (M / p) pb`](def/CuspForm_HeckeOperatorFormsGammaH.html#L36) of $pb$; a finite set $SS$ of pairs of places of $\bar F$ which, by `hSS`, consists exactly of the pairs in `ssNodePairsQExp`, i.e. pairs $(s_1,s_2)$ with $s_2$ a supersingular place and $s_1$ its `qExpFrobeniusPlaceModL`-image; a place specialisation datum `Psp` of type `JHPlaceSpecialization p M H hpM A` (a surjective map `sp` from places of $F'$ to places of $\bar F$ together with a homomorphism of degree-zero divisor class groups, subject to the compatibilities with $q$-expansions, with inertia and with Frobenius recorded in that structure); and a prolongation datum `Rpd` of type `ProlongationDatum Psp θ`, consisting of two regular prolongations `Rpd.R₁`, `Rpd.R₂` of $A$ to $F$ with residue maps to $\bar F$, where `R₁` reduces Laurent series coefficient-wise and membership in, and residues of, `R₂` are those of `R₁` transported through $\theta$. For a place $W$ of $F$ one writes `Psp.reduceFst α hα W` $=$ `Psp.sp` of the restriction of $W$ along $\alpha$, and `Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ W` $= \delta$ applied to `Psp.sp` of the restriction of $W$ along $\alpha$ followed by $\theta$.
--
--   The hypotheses on these data fall into the following groups.
--
--   Fixing and dichotomy: `hFix` asserts that every supersingular place $y$ in `ssPlacesQExp` and its Frobenius image `qExpFrobeniusPlaceModL` are `Fixed` for $\delta$, i.e. satisfy $\mathrm{Frob}(\delta(\mathrm{Frob}(v))) = v$; `hFixFin` asserts that the set of $\delta$-fixed places of $\bar F$ is finite; `hTD` is `Psp.TypeDichotomy`: for every place $W$ of $F$, either the first reduction of $W$ is the Frobenius image of its second reduction, or $\delta$ applied to the Frobenius image of its first reduction is its second reduction.
--
--   Model laws: `hmodel` is `Rpd.IsModel`, the conjunction of the two divisor laws `DivisorLawFst`, `DivisorLawSnd` and the two cusp laws `CuspLawInfty`, `CuspLawZero`; `hO` is `Rpd.OrderLawFixed`, stating that for $f \in F$ lying in both rings of integers with both residues non-zero, and for a divisor $D$ equal to the divisor of $f$, the push-forward along the first reduction of $D$ at a $\delta$-fixed affine place $v$ (affine in the sense of `IsAffinePlace`: $v$ has a value at a function whose Laurent series is `jqModC`) equals $\mathrm{ord}_v$ of the first residue plus $\mathrm{ord}$ of the second residue at $\delta(\mathrm{Frob}(v))$; `hreg` is `Rpd.RegularityLaw` for $SS$ (regularity of both residues at $\delta$-fixed affine places, and existence of a common value at each node, under the corresponding non-negativity of orders upstairs); `hnv` is `Rpd.NodeValueLaw` for $SS$ (for $f$ integral for both prolongations with non-zero residues and a node $s$ over which the divisor of $f$ is trivial, the two residues take a common non-zero value at $s_1$ and $s_2$).
--
--   Galois compatibility: `hθgal` asserts that $\theta$ commutes with the `arithmeticGalois` action of every automorphism $\sigma$ of $\overline{\mathbb Q}$ over $\mathbb Q$ on $F$.
--
--   Local order bounds `hLFst` and `hLSnd`: for two distinct places $Q \neq Q'$ of $F$ that are both `IsStrictFst` (respectively both `IsStrictSnd`) and have the same first (respectively second) reduction, that common reduction being an affine place, for a natural number $n$ non-zero in $\kappa$, and for $g$ in `Rpd.R₁.integers` (respectively `Rpd.R₂.integers`) with non-zero residue such that $\mathrm{ord}_Q g = -n$, $\mathrm{ord}_{Q'} g = n$ and $\mathrm{ord}_W g = 0$ for every other strict place $W$ with the same reduction, and for $e \in A$ and $\varepsilon$ in the same ring of integers with non-zero residue such that $g = 1 + e\varepsilon$: the order of the residue of $\varepsilon$ at the common reduced place is at least $-1$.
--
--   Units `hUnit`: there exist $u_1, u_2 \in F$ and divisors $D_1, D_2$ of $F$ with $D_i W = \mathrm{ord}_W u_i$ for all $W$, such that (i) $u_1$ and $u_1^{-1}$ lie in `Rpd.R₁.integers`, the residue of $u_1$ is non-zero, the push-forward along the first reduction of `Psp.fstDiv` of $D_1$ agrees at every non-$\delta$-fixed place $v$ with $\mathrm{ord}_v$ of that residue, and the push-forward along the first reduction of the part of $D_1$ supported on `IsInftySide` places agrees, at the first reduction of each infinity-side place $C$, with the order there of that residue; (ii) every non-zero $f \in F$ admits $m \neq 0$ and $j \in \mathbb Z$ with $f^m u_1^{\,j}$ in `Rpd.R₂.integers` of non-zero residue; (iii) the mirror statement for $u_2$, `Rpd.R₂`, `Psp.sndDiv` of $D_2$, the second reduction and `IsZeroSide` places; (iv) every non-zero $f \in F$ admits $m \neq 0$ and $j \in \mathbb Z$ with $f^m u_2^{\,j}$ in `Rpd.R₁.integers` of non-zero residue.
--
--   Cusps and orientation: `hcusp` asserts that every non-affine place $w$ of $\bar F$ is the first reduction of some infinity-side place and also the second reduction of some zero-side place; `horientInf` asserts that for every infinity-side place $C$, $\delta$ of the Frobenius image of its first reduction is its second reduction, and `horient0` that for every zero-side place $C$, its first reduction is the Frobenius image of its second reduction.
--
--   Annuli: a function $e$ on $SS$ with $e(s) > 0$ for all $s$ (`he`), and `hAnn`, which provides for each node $s = (s_1,s_2) \in SS$ an [`AlgebraicCurve.Annulus`](def/AlgebraicCurve_SemistableCharts.html#L86) $\mathrm{An}$ over $A$ in $F$ such that: its domain consists exactly of the places $W$ with first reduction $s_1$ that are neither `IsStrictFst` nor `IsStrictSnd`; its modulus is $p^{e(s)}$ times a unit of $A$; its parameter is invariant under the `arithmeticGalois` action of every element of the inertia subgroup `A.inertiaSubgroupIn ℚ`; the product of the inverse of the modulus with the parameter lies in `Rpd.R₁.integers`; the parameter lies in `Rpd.R₂.integers` with non-zero residue; the residue of the parameter has order $1$ at $s_2$, and for every $f \in$ `Rpd.R₂.integers` with non-zero residue and with $\mathrm{ord}_P f = 0$ at all $P$ in the domain, and every such $P$, the element $P(f)\cdot P(\mathrm{param})^{-\mathrm{ord}_{s_2}(\text{residue of } f)}$ (values taken via `Place.evalAt`) lies in $A$ and is a unit there; and the mirror clauses for `Rpd.R₁` with the function $\mathrm{modulus}\cdot\mathrm{param}^{-1}$ and the place $s_1$.
--
--   Finally, $S$ is a set of automorphisms of $\overline{\mathbb Q}$ over $\mathbb Q$ all lying in `A.inertiaSubgroupIn ℚ` (`hS`); $D$ is a divisor of $F$ with $0 \le D$ which is `Psp.IsGoodDiv`, i.e. every place in the support of $D$ is `IsStrictFst` or `IsStrictSnd` (`hgood`), and whose support is pointwise fixed by the `arithmeticGalois` action of every $\sigma \in S$ (`hDfix`); and $G \in F$ lies in `riemannRochSpace D` (for every place $v$, the adic valuation of $G$ at $v$ is at most $\exp(D v)$) and in both `Rpd.R₁.integers` and `Rpd.R₂.integers`.
--
--   Under these hypotheses the conclusion is the conjunction of three assertions: first, the image of $G$ under `Rpd.R₁.residue`, viewed in $\bar F$, lies in the Riemann–Roch space of the push-forward along `Psp.reduceFst α hα` of `Psp.fstDiv` of $D$ (the restriction of $D$ to its strict-first places); second, the image of $G$ under `Rpd.R₂.residue` lies in the Riemann–Roch space of the push-forward along `Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ` of `Psp.sndDiv` of $D$ (the restriction of $D$ to its strict-second places); third, for every node $s \in SS$ there is a scalar $c \in \kappa$ such that $s_1$ has value $c$ at the first residue of $G$ and $s_2$ has value $c$ at the second residue of $G$, where `Place.HasValue v g c` means that $g$ lies in the valuation ring of $v$ and its residue is the image of $c$ in the residue field of $v$. No non-vanishing of $c$ is asserted.
--
--   This is the level-$\Gamma_H(M)$ form of the reduction statement for sections of a Riemann–Roch space along a good divisor: the two residues of a function with poles bounded by $D$ have poles bounded by the two reduced divisors on the components of the fibre at $p$, and they glue at the supersingular nodes. It is used in the construction of Galois-equivariant node-compatible pairs of residues, in the description of the special fibre of $X_H(M)$ at a prime exactly dividing the level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHPlaceSpecialization_ProlongationDatum_IsModel_residue_mem_riemannRochSpace_mapDomain_and_node_hasValue_of_isGoodDiv.lean

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_AdelicIndex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve.JHNeronObjectAtP
open ModularCurve
open scoped MatrixGroups

open Classical in

theorem ModularCurve.JHPlaceSpecialization.ProlongationDatum.IsModel.residue_mem_riemannRochSpace_mapDomain_and_node_hasValue_of_isGoodDiv
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
    (G : ↥(xHFunctionFieldBar M H)) (hG : G ∈ riemannRochSpace D) (hG₁ : G ∈ Rpd.R₁.integers) (hG₂ : G ∈ Rpd.R₂.integers) :
    (Rpd.R₁.residue ⟨G, hG₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) ∈ riemannRochSpace (Finsupp.mapDomain (Psp.reduceFst α hα) (Psp.fstDiv α (θ.toAlgHom.comp α) hα hβ δ D)) ∧
    (Rpd.R₂.residue ⟨G, hG₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) ∈ riemannRochSpace (Finsupp.mapDomain (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ) (Psp.sndDiv α (θ.toAlgHom.comp α) hα hβ δ D)) ∧
    ∀ s ∈ SS, ∃ c : ResidueField ↥A,
      s.1.HasValue (Rpd.R₁.residue ⟨G, hG₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) c ∧ s.2.HasValue (Rpd.R₂.residue ⟨G, hG₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) c := by sorry
