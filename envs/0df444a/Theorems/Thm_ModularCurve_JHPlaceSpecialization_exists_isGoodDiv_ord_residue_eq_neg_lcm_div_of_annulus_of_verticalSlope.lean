-- Prove2me | Theorems.Thm_ModularCurve_JHPlaceSpecialization_exists_isGoodDiv_ord_residue_eq_neg_lcm_div_of_annulus_of_verticalSlope
-- name    : ModularCurve.JHPlaceSpecialization.exists_isGoodDiv_ord_residue_eq_neg_lcm_div_of_annulus_of_verticalSlope
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/21033c8b-96c0-5af8-a9a6-fc0838b6ea03
-- title:
--   Good function with node residue orders -lcm(e)/e(s)
-- statement:
--   Throughout, $p$ is a prime and $M$ a non-zero natural number with $p \mid M$ (`hpM`) but $p^2 \nmid M$ (`hpM2`), so $p \parallel M$; $H$ is a subgroup of $(\mathbb{Z}/M)^\times$ which, by `hHp`, contains every unit whose image under the reduction map $(\mathbb{Z}/M)^\times \to (\mathbb{Z}/(M/p))^\times$ is trivial. $A$ is a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` lying over $p$ in the sense that $p$ is a non-unit of $A$ (`hA`), with residue field $\kappa =$ `ResidueField A` of characteristic $p$ and algebraically closed. Write $F_M$ for `xHFunctionFieldBar M H`, the base change to $\overline{\mathbb{Q}}$ of the field of modular functions of level $\Gamma_H(M)$ inside Laurent series, $F_{M/p}$ for `xHFunctionFieldBar (M/p) (infSubgroup p M H hpM)`, where `infSubgroup` is the image of $H$ in $(\mathbb{Z}/(M/p))^\times$, and $\bar F$ for `Fbar p M H hpM κ`, the $q$-expansion function field `qExpFunctionFieldC κ (ΓN p M H hpM)` over $\kappa$.
--
--   The geometric data are: an automorphism $\theta$ of $F_M$ over $\overline{\mathbb{Q}}$; an integral $\overline{\mathbb{Q}}$-algebra map $\alpha : F_{M/p} \to F_M$ (`hα`) such that $\theta \circ \alpha$ is integral as well (`hβ`); the normalisations `hα_coe`, that $\alpha$ is the identity on underlying Laurent series, and `hβ_coe`, that $\theta \circ \alpha$ acts on Laurent series as `qExpand` for $p$, i.e. $q \mapsto q^p$; a unit $pb$ of $\mathbb{Z}/(M/p)$ whose underlying element is $p$ (`hpb`); and a self-map $\delta$ of the places of $\bar F$ over $\kappa$ which, by `hδ`, is the action on places of the semilinear automorphism attached to the diamond automorphism `diamondActionModL κ (M/p) (infSubgroup p M H hpM)` evaluated at [`CuspForm.gammaLift (M/p) pb`](def/CuspForm_HeckeOperatorFormsGammaH.html#L36). The finite set $SS$ of pairs of places of $\bar F$ is, by `hSS`, exactly `ssNodePairsQExp κ (ΓN p M H hpM) p`: pairs $s$ with $s_2$ a supersingular $q$-expansion place and $s_1$ its image under the mod-$p$ Frobenius place map `qExpFrobeniusPlaceModL`.
--
--   The specialization data are a `JHPlaceSpecialization p M H hpM A`, written $Psp$, consisting of a map $sp$ from places of $F_{M/p}$ to places of $\bar F$ together with its degree-zero divisor class map and the compatibilities recorded in that structure, and a `ProlongationDatum Psp θ`, written $Rpd$, consisting of two regular prolongations $R_1, R_2$ of $A$ in $F_M$ with residues into $\bar F$, the $q$-expansion compatibility of $R_1$, and the identification of $R_2$ with the $\theta$-transport of $R_1$. For a place $W$ of $F_M$, `reduceFst` is $sp$ applied to the restriction of $W$ along $\alpha$, and `reduceSnd` is $\delta$ applied to $sp$ of the restriction along $\theta \circ \alpha$; $W$ is strict-first when $\delta(\mathrm{Frob}(\mathrm{red}_1 W)) = \mathrm{red}_2 W$ and $\mathrm{red}_1 W$ is not $\delta$-fixed, strict-second when $\mathrm{red}_1 W = \mathrm{Frob}(\mathrm{red}_2 W)$ and $\mathrm{red}_2 W$ is not $\delta$-fixed, where $\mathrm{Frob} =$ `qExpFrobeniusPlaceModL` and a place $v$ is $\delta$-fixed (`Fixed`) when $\mathrm{Frob}(\delta(\mathrm{Frob}\, v)) = v$.
--
--   The hypotheses on these data are: `hFix`, that every supersingular place $y$ in `ssPlacesQExp κ (ΓN p M H hpM) p` and its Frobenius image are $\delta$-fixed; `hTD`, the type dichotomy, that every place $W$ of $F_M$ satisfies $\mathrm{red}_1 W = \mathrm{Frob}(\mathrm{red}_2 W)$ or $\delta(\mathrm{Frob}(\mathrm{red}_1 W)) = \mathrm{red}_2 W$; `hmodel`, that $Rpd$ is a model for $(\alpha, \theta\circ\alpha, \delta)$, i.e. the two divisor laws and the two cusp laws hold; `hO`, the order law at $\delta$-fixed affine places, expressing the `reduceFst` push-forward of the divisor of a function integral and of non-zero residue for both prolongations as the sum of the order of its $R_1$-residue at $v$ and of its $R_2$-residue at $\delta(\mathrm{Frob}\, v)$; `hreg`, the regularity law at $SS$; `hnv`, the node value law at $SS$, giving a common non-zero value of the two residues at the two members of a node pair; `hθgal`, that $\theta$ commutes with the arithmetic Galois action of $\mathrm{Aut}(\overline{\mathbb{Q}}/\mathbb{Q})$ on $F_M$; and `hFixFin`, that the set of $\delta$-fixed places of $\bar F$ is finite.
--
--   Two one-sided local bounds are assumed. `hLFst` states: for distinct strict-first places $Q, Q'$ with the same `reduceFst` image, that image being an affine place (a place finite on an element with $q$-expansion `jqModC`), for a natural number $n$ with non-zero image in $\kappa$, for $g$ in the integers of $R_1$ with non-zero $R_1$-residue such that $\operatorname{ord}_Q g = -n$, $\operatorname{ord}_{Q'} g = n$ and $\operatorname{ord}_W g = 0$ for every other strict-first $W$ over the same image, and for $e \in A$ and $\varepsilon$ in the integers of $R_1$ with non-zero residue such that $g = 1 + e\,\varepsilon$, the order at $\mathrm{red}_1 Q$ of the $R_1$-residue of $\varepsilon$ is at least $-1$. The hypothesis `hLSnd` is the same statement with strict-second places, `reduceSnd` and $R_2$ in place of strict-first places, `reduceFst` and $R_1$.
--
--   The hypothesis `hUnit` asserts the existence of $u_1, u_2 \in F_M$ and divisors $D_1, D_2$ on $F_M$ with $D_i(W) = \operatorname{ord}_W u_i$ for all $W$, such that: $u_1$ and $u_1^{-1}$ lie in the integers of $R_1$ with $R_1$-residue of $u_1$ non-zero, the `reduceFst` push-forward of the strict-first part of $D_1$ agrees at every non-$\delta$-fixed place $v$ with the order at $v$ of that residue, and the `reduceFst` push-forward of the part of $D_1$ supported on infinity-side places agrees at $\mathrm{red}_1 C$ with the order there of that residue, for every infinity-side $C$; every non-zero $f \in F_M$ admits $m \neq 0$ and $j \in \mathbb{Z}$ with $f^m u_1^{\,j}$ in the integers of $R_2$ of non-zero $R_2$-residue; and the two symmetric clauses with $u_2$, $R_2$, `reduceSnd`, the strict-second part of $D_2$, zero-side places, and $f^m u_2^{\,j}$ integral of non-zero residue for $R_1$. Here a place of $F_M$ is infinity-side (`IsInftySide`) when it is cuspidal and takes a value with residue $1$ on $x'/x^p$, where $x$ has $q$-expansion `jqModC` and $x'$ its $p$-fold expansion, and zero-side (`IsZeroSide`) when it is cuspidal in the second sense and takes such a value on $x/x'^p$. The hypothesis `hcusp` states that every non-affine place $w$ of $\bar F$ is the `reduceFst` image of some infinity-side place and the `reduceSnd` image of some zero-side place, and the orientation hypotheses `horientInf`, `horient0` state that $\delta(\mathrm{Frob}(\mathrm{red}_1 C)) = \mathrm{red}_2 C$ for infinity-side $C$ and $\mathrm{red}_1 C = \mathrm{Frob}(\mathrm{red}_2 C)$ for zero-side $C$.
--
--   Widths are given by $e : SS \to \mathbb{N}$ with $e(s) > 0$ (`he`). The annulus hypothesis `hAnn` asserts, for each $s \in SS$, the existence of an annulus $An$ over $A$ in $F_M$ (in the sense of [`AlgebraicCurve.Annulus`](def/AlgebraicCurve_SemistableCharts.html#L86)) such that: its domain consists exactly of the places $W$ with $\mathrm{red}_1 W = s_1$ which are neither strict-first nor strict-second; its modulus is $p^{e(s)}$ times a unit of $A$; its parameter is fixed by the arithmetic Galois action of the inertia subgroup of $A$ over $\mathbb{Q}$; the product of the inverse of the modulus with the parameter lies in the integers of $R_1$; the parameter lies in the integers of $R_2$ with non-zero residue, the order at $s_2$ of that residue is $1$, and for every $f$ integral of non-zero residue for $R_2$ with $\operatorname{ord}_P f = 0$ on the domain, and every $P$ in the domain, the value $P(f)\cdot P(\text{param})^{-\operatorname{ord}_{s_2}(\overline f)}$ lies in $A$ and is a unit there; and the mirror clause for $R_1$ and $s_1$ with the flipped parameter $\text{modulus}\cdot\text{param}^{-1}$.
--
--   The vertical-slope hypothesis `hVSlope` assumes, for every family of annuli $An : SS \to$ `Annulus A F_M` satisfying for each $s$ the list of properties just described, and every $k \in \mathbb{N}$ divisible by all $e(s)$, the existence of $f \in F_M$ and $c \in \overline{\mathbb{Q}}$ with $c \cdot f$ in the integers of $R_1$, such that $f \neq 0$, the $R_1$-residue of $c\cdot f$ is non-zero, every divisor $G$ of $f$ is good (every place in its support is strict-first or strict-second), $\operatorname{ord}_V f = 0$ whenever $\mathrm{red}_1 V$ is $\delta$-fixed and differs from all $s_1$, the order of the residue of $c\cdot f$ vanishes at every $\delta$-fixed place $v$ distinct from all $s_1$, and for each $s$ there is $a \neq 0$ in $\overline{\mathbb{Q}}$ with $\operatorname{ord}_P f = 0$ and $P(f)\,a\,P(\text{param of } An\,s)^{-(k/e(s))}$ a unit of $A$ for every $P$ in the domain of $An\,s$.
--
--   Finally, four one-sided push-forward laws are assumed: `hOSFst` and `hOSInf`, that for $g$ in the integers of $R_1$ with non-zero residue and $E$ the divisor of $g$, the `reduceFst` push-forward of the strict-first part of $E$ at any non-$\delta$-fixed place $v$, respectively the `reduceFst` push-forward of the infinity-side part of $E$ at $\mathrm{red}_1 c$ for infinity-side $c$, equals the order of the $R_1$-residue of $g$ at the place in question; and `hOSSnd`, `hOSZero`, the corresponding statements for $R_2$, `reduceSnd`, strict-second places and zero-side places.
--
--   Under these hypotheses there exist $f \in F_M$ with $f \neq 0$, a constant $c \in \overline{\mathbb{Q}}$ and a proof that $c \cdot f$ lies in the integers of $R_1$, such that: first, the $R_1$-residue of $c \cdot f$ is non-zero; second, every divisor $G$ on $F_M$ with $G(V) = \operatorname{ord}_V f$ for all $V$ is a good divisor for $(Psp, \alpha, \theta\circ\alpha, \delta)$, that is, each place in its support is strict-first or strict-second; third, for every $s \in SS$ the order at $s_1$ of the $R_1$-residue of $c\cdot f$ equals $-\bigl(\operatorname{lcm}_{t \in SS} e(t)\bigr)/e(s)$, the least common multiple being taken over all of $SS$; and fourth, for every divisor $G$ of $f$ and every place $v$ of $\bar F$ over $\kappa$ with $v \neq s_1$ for all $s \in SS$, the `reduceFst` push-forward of the strict-first part of $G$ at $v$ equals the order at $v$ of the $R_1$-residue of $c\cdot f$.
--
--   This produces, on the $\Gamma_H(M)$ side with $p \parallel M$, a modular function whose divisor is supported on the strict places of the two components and whose residue on the first component has order $-\operatorname{lcm}(e)/e(s)$ at each supersingular node and the expected push-forward orders away from the nodes, the vertical-slope clause supplying the function and the annuli supplying the widths $e(s)$. It is used by [`ModularCurve.JHPlaceSpecialization.exists_isPrincipal_isGoodDiv_degree_fstDiv_eq_sum_lcm_div_of_annulus_of_verticalSlope`](thm.html#ModularCurve.JHPlaceSpecialization.exists_isPrincipal_isGoodDiv_degree_fstDiv_eq_sum_lcm_div_of_annulus_of_verticalSlope), in the analysis of the fibre of the Néron model of $J_H(M)$ at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHPlaceSpecialization_exists_isGoodDiv_ord_residue_eq_neg_lcm_div_of_annulus_of_verticalSlope.lean

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

theorem ModularCurve.JHPlaceSpecialization.exists_isGoodDiv_ord_residue_eq_neg_lcm_div_of_annulus_of_verticalSlope
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
            (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ c).ord (Rpd.R₂.residue ⟨g, h₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))) :
    ∃ (f : ↥(xHFunctionFieldBar M H)) (_ : f ≠ 0) (c : AlgebraicClosure ℚ) (hc : c • f ∈ Rpd.R₁.integers),
      Rpd.R₁.residue ⟨c • f, hc⟩ ≠ 0 ∧
      (∀ G : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), (∀ V, G V = V.ord f) → Psp.IsGoodDiv α (θ.toAlgHom.comp α) hα hβ δ G) ∧
      (∀ s : ↥SS, s.1.1.ord (Rpd.R₁.residue ⟨c • f, hc⟩ : Fbar p M H hpM (ResidueField ↥A)) = -((Finset.univ.lcm e / e s : ℕ) : ℤ)) ∧
      (∀ G : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), (∀ V, G V = V.ord f) →
        ∀ v : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)), (∀ s ∈ SS, v ≠ s.1) →
          Finsupp.mapDomain (Psp.reduceFst α hα) (Psp.fstDiv α (θ.toAlgHom.comp α) hα hβ δ G) v =
            v.ord (Rpd.R₁.residue ⟨c • f, hc⟩ : Fbar p M H hpM (ResidueField ↥A))) := by sorry
