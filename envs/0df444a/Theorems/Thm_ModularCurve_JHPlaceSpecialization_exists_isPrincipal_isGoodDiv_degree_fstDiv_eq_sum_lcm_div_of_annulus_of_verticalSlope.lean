-- Prove2me | Theorems.Thm_ModularCurve_JHPlaceSpecialization_exists_isPrincipal_isGoodDiv_degree_fstDiv_eq_sum_lcm_div_of_annulus_of_verticalSlope
-- name    : ModularCurve.JHPlaceSpecialization.exists_isPrincipal_isGoodDiv_degree_fstDiv_eq_sum_lcm_div_of_annulus_of_verticalSlope
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/ed83bb48-f976-5087-bad7-dc453e168a45
-- title:
--   Principal good divisor of bidegree (m(e),-m(e)) from vertical slopes
-- statement:
--   Fix a prime $p$ and a modulus $M$ with $p \mid M$ (`hpM`) and $p^2 \nmid M$ (`hpM2`), and a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit whose image in $(\mathbb{Z}/(M/p))^\times$ is trivial (`hHp`). Let $A$ be a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` lying over $p$, i.e. $p$ is a non-unit of $A$ (`hA`), whose residue field $\kappa =$ `ResidueField ↥A` has characteristic $p$ and is algebraically closed. Write $FM =$ `xHFunctionFieldBar M H` for the base change to $\overline{\mathbb{Q}}$ of the $\Gamma_H(M)$ function field inside Laurent series, $FMp$ for the corresponding field at level $M/p$ with the image subgroup `infSubgroup p M H hpM`, and $Fb =$ `Fbar p M H hpM κ` for the $q$-expansion function field of `ΓN p M H hpM` over $\kappa$.
--
--   The data are: an $\overline{\mathbb{Q}}$-algebra automorphism $\theta$ of $FM$; an integral $\overline{\mathbb{Q}}$-algebra map $\alpha : FMp \to FM$ (`hα`) with $\beta = \theta \circ \alpha$ also integral (`hβ`), where $\alpha$ is the inclusion of $q$-expansions (`hα_coe`: the Laurent series of $\alpha u$ is that of $u$) and $\beta$ is the substitution $q \mapsto q^p$ (`hβ_coe`: the Laurent series of $\beta u$ is `qExpand _ p` applied to that of $u$); a unit $pb \in (\mathbb{Z}/(M/p))^\times$ reducing to $p$ (`hpb`); the map $\delta$ on places of $Fb$ given (`hδ`) by the semilinear action of the diamond automorphism `diamondActionModL κ (M/p) (infSubgroup p M H hpM)` evaluated at a $\Gamma_0(M/p)$-lift of $pb$; a finite set $SS$ of pairs of places of $Fb$ whose members are exactly the supersingular node pairs `ssNodePairsQExp κ (ΓN p M H hpM) p`, that is the pairs $(\mathrm{Frob}\, v, v)$ with $v$ supersingular (`hSS`); a place specialisation $Psp$ of type `JHPlaceSpecialization p M H hpM A` (a map $\mathrm{sp}$ from places of $FMp$ to places of $Fb$ together with a map on $\mathrm{Pic}^0$ and its compatibility axioms); and a prolongation datum $Rpd$ for $Psp$ and $\theta$, consisting of two regular prolongations $R_1, R_2$ of $A$ in $FM$ with values in $Fb$, linked by $f \in R_2.\mathrm{integers} \iff \theta f \in R_1.\mathrm{integers}$ and $R_2$-residue of $f$ equal to the $R_1$-residue of $\theta f$. Throughout, $\mathrm{Frob}$ denotes `qExpFrobeniusPlaceModL κ (ΓN p M H hpM) p`, a place $v$ of $Fb$ is *fixed* when $\mathrm{Frob}(\delta(\mathrm{Frob}\, v)) = v$, $\mathrm{red}_1 W = \mathrm{sp}(W|_\alpha)$ and $\mathrm{red}_2 W = \delta(\mathrm{sp}(W|_\beta))$ for a place $W$ of $FM$, $W$ is *strict of the first kind* when $\delta(\mathrm{Frob}(\mathrm{red}_1 W)) = \mathrm{red}_2 W$ and $\mathrm{red}_1 W$ is not fixed, *strict of the second kind* when $\mathrm{red}_1 W = \mathrm{Frob}(\mathrm{red}_2 W)$ and $\mathrm{red}_2 W$ is not fixed, and `fstDiv`, `sndDiv` are the restrictions of a divisor to the places strict of the first, respectively second, kind.
--
--   The hypotheses fall into the following groups.
--
--   (i) Structural laws at the supersingular locus: `hFix`, every supersingular place $y$ and its Frobenius image are fixed; `hTD` (type dichotomy), every place $W$ of $FM$ satisfies $\mathrm{red}_1 W = \mathrm{Frob}(\mathrm{red}_2 W)$ or $\delta(\mathrm{Frob}(\mathrm{red}_1 W)) = \mathrm{red}_2 W$; `hmodel`, the four clauses `DivisorLawFst`, `DivisorLawSnd`, `CuspLawInfty`, `CuspLawZero` of `IsModel` for $Rpd$; `hO` (`OrderLawFixed`), for $f$ lying in both prolongations with non-zero residues and $D$ the divisor of $f$, the push-forward of $D$ along $\mathrm{red}_1$ at a fixed affine place $v$ equals $v.\mathrm{ord}$ of the $R_1$-residue plus $\delta(\mathrm{Frob}\,v).\mathrm{ord}$ of the $R_2$-residue; `hreg` (`RegularityLaw` for $SS$, two clauses: non-negativity of the two residue orders at fixed affine places, and joint attainment of a common value at each node pair, whenever the divisor of $f$ is non-negative above the relevant place); `hnv` (`NodeValueLaw` for $SS$: for a node $s$ with no place $V$ of non-zero order mapping to $(s_1,s_2)$ under $(\mathrm{red}_1,\mathrm{red}_2)$, the two residues take a common non-zero value $c$ at $s_1$ and $s_2$). Here a place $v$ of $Fb$ is affine (`IsAffinePlace`) when $v$ takes a value at an element of $Fb$ whose $q$-expansion is `jqModC κ`.
--
--   (ii) Galois equivariance and finiteness: `hθgal`, $\theta$ commutes with the semilinear `arithmeticGalois` action of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ on $FM$; `hFixFin`, the set of $\delta$-fixed places of $Fb$ is finite.
--
--   (iii) Two local bounds `hLFst` and `hLSnd`, one for each side. `hLFst`: if $Q \neq Q'$ are both strict of the first kind with the same, affine, reduction $\mathrm{red}_1 Q$; $n$ is a natural number non-zero in $\kappa$; $g \in R_1.\mathrm{integers}$ has non-zero $R_1$-residue, $Q.\mathrm{ord}\, g = -n$, $Q'.\mathrm{ord}\, g = n$ and every further place $W$ strict of the first kind with $\mathrm{red}_1 W = \mathrm{red}_1 Q$, $W \neq Q$, $W \neq Q'$ has $W.\mathrm{ord}\, g = 0$; and $g = 1 + e\,\varepsilon$ for some $e \in A$ and some $\varepsilon \in R_1.\mathrm{integers}$ with non-zero $R_1$-residue; then $(\mathrm{red}_1 Q).\mathrm{ord}$ of the $R_1$-residue of $\varepsilon$ is at least $-1$. `hLSnd` is the same statement with $R_1$, $\mathrm{red}_1$ and strictness of the first kind replaced by $R_2$, $\mathrm{red}_2$ and strictness of the second kind.
--
--   (iv) A unit hypothesis `hUnit`: there exist $u_1, u_2 \in FM$ and divisors $D_1, D_2$ with $D_i W = W.\mathrm{ord}\, u_i$ for all $W$, such that $u_1$ and $u_1^{-1}$ lie in $R_1.\mathrm{integers}$ with non-zero $R_1$-residue of $u_1$, the push-forward along $\mathrm{red}_1$ of `fstDiv` $D_1$ agrees at every non-fixed place $v$ with $v.\mathrm{ord}$ of that residue, and the push-forward along $\mathrm{red}_1$ of the restriction of $D_1$ to the infinity-side places agrees at $\mathrm{red}_1 C$, for every infinity-side $C$, with $(\mathrm{red}_1 C).\mathrm{ord}$ of that residue; every non-zero $f$ admits $m \neq 0$ and $j \in \mathbb{Z}$ with $f^m u_1^{\,j} \in R_2.\mathrm{integers}$ of non-zero $R_2$-residue; and the mirror clauses for $u_2$, with $R_2$, $\mathrm{red}_2$, `sndDiv` $D_2$, the zero-side places, and $f^m u_2^{\,j} \in R_1.\mathrm{integers}$ of non-zero $R_1$-residue. (A place $C$ of $FM$ is infinity-side when it is cuspidal and takes at $x'/x^p$, for $x, x'$ of $q$-expansions $j(q)$ and $j(q^p)$, a value in $A$ with residue $1$; it is zero-side when the corresponding condition holds with `IsCuspidal'` and $x/x'^p$.)
--
--   (v) Cusp and orientation hypotheses: `hcusp`, every non-affine place $w$ of $Fb$ is $\mathrm{red}_1$ of some infinity-side place and $\mathrm{red}_2$ of some zero-side place; `horientInf`, $\delta(\mathrm{Frob}(\mathrm{red}_1 C)) = \mathrm{red}_2 C$ for infinity-side $C$; `horient0`, $\mathrm{red}_1 C = \mathrm{Frob}(\mathrm{red}_2 C)$ for zero-side $C$.
--
--   (vi) Widths and annuli: a function $e : SS \to \mathbb{N}$ with $e(s) > 0$ (`he`), and `hAnn`, asserting for each node $s \in SS$ the existence of an annulus $An$ of $FM$ along $A$ (in the sense of [`AlgebraicCurve.Annulus`](def/AlgebraicCurve_SemistableCharts.html#L86)) such that: its domain consists exactly of the places $W$ with $\mathrm{red}_1 W = s_1$ that are strict of neither kind; its modulus is $p^{e(s)}$ times a unit of $A$; its parameter is invariant under the `arithmeticGalois` action of the inertia subgroup of $A$ over $\mathbb{Q}$; $(\mathrm{modulus})^{-1}\cdot\mathrm{param}$ lies in $R_1.\mathrm{integers}$; $\mathrm{param}$ lies in $R_2.\mathrm{integers}$ with non-zero residue; the $R_2$-residue of $\mathrm{param}$ has order $1$ at $s_2$, and for every $f \in R_2.\mathrm{integers}$ with non-zero residue and with $P.\mathrm{ord}\, f = 0$ on the whole domain, $P.\mathrm{evalAt} f \cdot (P.\mathrm{evalAt}\,\mathrm{param})^{-s_2.\mathrm{ord}(\text{residue of } f)}$ is a unit of $A$ at every $P$ in the domain; and the mirror clause on the first side for $\mathrm{modulus}\cdot\mathrm{param}^{-1}$, whose $R_1$-residue has order $1$ at $s_1$ and which yields the analogous unit statement with $s_1$ and $R_1$.
--
--   (vii) The vertical-slope hypothesis `hVSlope`: for every family $An$ of annuli indexed by $SS$ satisfying the clauses just listed, and every $k \in \mathbb{N}$ divisible by all $e(s)$, there exist $f \in FM$ and $c \in \overline{\mathbb{Q}}$ with $c \cdot f \in R_1.\mathrm{integers}$, such that $f \neq 0$, the $R_1$-residue of $c\cdot f$ is non-zero, every divisor $G$ with $G V = V.\mathrm{ord}\, f$ is good for $Psp$, $V.\mathrm{ord}\, f = 0$ for every place $V$ whose $\mathrm{red}_1$-image is fixed and is not any $s_1$ with $s \in SS$, the order at $v$ of the $R_1$-residue of $c \cdot f$ vanishes for every fixed place $v$ distinct from all $s_1$, and for every $s \in SS$ there is $a \neq 0$ in $\overline{\mathbb{Q}}$ with $P.\mathrm{ord}\, f = 0$ and $P.\mathrm{evalAt} f \cdot a \cdot (P.\mathrm{evalAt}\,(An\,s).\mathrm{param})^{-(k/e(s))}$ a unit of $A$, for all $P$ in the domain of $An\,s$.
--
--   (viii) Four one-sided push-forward laws: `hOSFst` and `hOSSnd`, for $g$ in $R_1$ (respectively $R_2$) with non-zero residue and $E$ the divisor of $g$, the push-forward along $\mathrm{red}_1$ of `fstDiv` $E$ (respectively along $\mathrm{red}_2$ of `sndDiv` $E$) agrees at every non-fixed place $v$ with $v.\mathrm{ord}$ of the residue of $g$; and `hOSInf`, `hOSZero`, the same equalities for the restriction of $E$ to the infinity-side (respectively zero-side) places, evaluated at $\mathrm{red}_1 c$ (respectively $\mathrm{red}_2 c$) for $c$ infinity-side (respectively zero-side).
--
--   Under these hypotheses there exists a divisor $G$ of $FM$ over $\overline{\mathbb{Q}}$ with the following four properties: $G$ is principal, i.e. there is $f \neq 0$ with $G v = v.\mathrm{ord}\, f$ for every place $v$; $G$ is good, i.e. every place in its support is strict of the first or of the second kind; the degree of `fstDiv` $G$ equals the integer $\sum_{s \in SS} \mathrm{lcm}_{t \in SS}\, e(t)\,/\,e(s)$; and the degree of `sndDiv` $G$ equals the negative of that integer.
--
--   This is the bidegree statement for a principal divisor adapted to the two-component semistable reduction of $X_H(M)$ at a prime $p$ with $p \parallel M$: from annuli of modulus $p^{e(s)}$ at the supersingular nodes and the vertical-slope clause it produces a principal good divisor whose strict-first and strict-second parts have degrees $\pm m(e)$ with $m(e) = \sum_s \mathrm{lcm}(e)/e(s)$. It is the $\Gamma_H$-level counterpart of the corresponding statement at level $\Gamma_0(Nq)$, and it feeds the component-group package for $J_H(M)$ at $p$ used in the level-lowering step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHPlaceSpecialization_exists_isPrincipal_isGoodDiv_degree_fstDiv_eq_sum_lcm_div_of_annulus_of_verticalSlope.lean

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

theorem ModularCurve.JHPlaceSpecialization.exists_isPrincipal_isGoodDiv_degree_fstDiv_eq_sum_lcm_div_of_annulus_of_verticalSlope
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
    ∃ G : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
      Divisor.IsPrincipal G ∧ Psp.IsGoodDiv α (θ.toAlgHom.comp α) hα hβ δ G ∧
        (Psp.fstDiv α (θ.toAlgHom.comp α) hα hβ δ G).degree = ((∑ s : ↥SS, Finset.univ.lcm e / e s : ℕ) : ℤ) ∧
        (Psp.sndDiv α (θ.toAlgHom.comp α) hα hβ δ G).degree = -((∑ s : ↥SS, Finset.univ.lcm e / e s : ℕ) : ℤ) := by sorry
