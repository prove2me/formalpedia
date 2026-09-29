-- Prove2me | Theorems.Thm_ModularCurve_JHPlaceSpecialization_exists_rep_forall_exists_ord_sub_pos_residue_notMem_of_isModel_of_regularityLaw_of_orderLawFixed_of_coe_of_unit_of_cusp_of_orient
-- name    : ModularCurve.JHPlaceSpecialization.exists_rep_forall_exists_ord_sub_pos_residue_notMem_of_isModel_of_regularityLaw_of_orderLawFixed_of_coe_of_unit_of_cusp_of_orient
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/f980fedc-04fc-5d5c-8613-8100594ccd15
-- title:
--   Representatives of J_H classes with non-supersingular j-values on supports
-- statement:
--   Throughout, $p$ is a prime and $M$ a nonzero natural number with $p \mid M$ (`hpM`) and $p^2 \nmid M$ (`hpM2`), so that $p$ exactly divides $M$, and $M/p$ is nonzero; $H$ is a subgroup of $(\mathbb{Z}/M)^\times$ containing the kernel of reduction to $(\mathbb{Z}/(M/p))^\times$, i.e. every unit $u$ with `ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1` lies in $H$ (`hHp`). Further, $A$ is a valuation subring of $\overline{\mathbb{Q}}$ lying over $p$ in the sense of `LiesOverPrime`, namely $p$ is a non-unit of $A$ (`hA`), and the residue field $\kappa =$ `ResidueField ↥A` is of characteristic $p$ and algebraically closed. Write $F_M =$ `xHFunctionFieldBar M H` for the base change to $\overline{\mathbb{Q}}$ of the function field `xHFunctionField M H` inside Laurent series, $F_{M/p} =$ `xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)` for the corresponding field at level $M/p$ with $H$ pushed forward along reduction, and $\bar F =$ `JHNeronObjectAtP.Fbar p M H hpM κ` for the characteristic-$p$ $q$-expansion function field of `JHNeronObjectAtP.ΓN p M H hpM` over $\kappa$. Places are places in the sense of [`AlgebraicCurve.Place`](def/AlgebraicCurve_DivisorClassGroup.html#L22) (valuation subrings containing the base field, proper, with principal-ideal valuation ring), `ord` is the associated normalised valuation, and $\varphi =$ `qExpFrobeniusPlaceModL κ (JHNeronObjectAtP.ΓN p M H hpM) p` is restriction of places along the mod-$p$ Frobenius of $\bar F$.
--
--   The specialisation kit consists of: a $\overline{\mathbb{Q}}$-algebra automorphism $\theta$ of $F_M$; two integral $\overline{\mathbb{Q}}$-algebra homomorphisms $\alpha, \beta : F_{M/p} \to F_M$ (`hα`, `hβ`); a unit $pb$ of $\mathbb{Z}/(M/p)$ whose underlying element is $p$ (`hpb`); a self-map $\delta$ of the set of places of $\bar F$ which by `hδ` is the action on places of the semilinear automorphism attached to the diamond automorphism `diamondActionModL κ (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)`; a finite set $SS$ of pairs of places of $\bar F$ which by `hSS` is exactly `ssNodePairsQExp κ (JHNeronObjectAtP.ΓN p M H hpM) p`, the set of pairs $s$ with $s_2$ a supersingular place and $s_1 = \varphi(s_2)$; a place specialisation `Psp` of type `JHPlaceSpecialization p M H hpM A`, giving a surjection `sp` from places of $F_{M/p}$ to places of $\bar F$ together with its divisor-, Pic$^0$-, inertia- and Frobenius-compatibilities; and a prolongation datum `Rpd` for `Psp` and $\theta$, consisting of two regular prolongations $R_1, R_2$ of $A$ to $F_M$ with residue maps into $\bar F$, the $q$-expansion compatibility of $R_1$, and the identifications $f \in R_2$ iff $\theta f \in R_1$ with matching residues. For a place $W$ of $F_M$, `Psp.reduceFst α hα W` is `sp` applied to the restriction of $W$ along $\alpha$, and `Psp.reduceSnd β hβ δ W` is $\delta$ applied to `sp` of the restriction of $W$ along $\beta$; $W$ is of strictly first type when $\delta(\varphi(\mathrm{red}_1 W)) = \mathrm{red}_2 W$ and $\mathrm{red}_1 W$ is not $\delta$-fixed (`Fixed δ v` meaning $\varphi(\delta(\varphi v)) = v$), and of strictly second type when $\mathrm{red}_1 W = \varphi(\mathrm{red}_2 W)$ and $\mathrm{red}_2 W$ is not $\delta$-fixed.
--
--   The structural laws imposed are: `hTD`, the type dichotomy, that every place of $F_M$ satisfies $\mathrm{red}_1 W = \varphi(\mathrm{red}_2 W)$ or $\delta(\varphi(\mathrm{red}_1 W)) = \mathrm{red}_2 W$; `hFix`, finiteness of the set of $\delta$-fixed places of $\bar F$; `hmodel`, that `Rpd` is a model, i.e. the two divisor laws (for $f$ with nonzero residues under both prolongations, the pushforward along $\mathrm{red}_1$ of the strictly-first-type part of the divisor of $f$ computes the order of the $R_1$-residue of $f$ at every non-fixed place, and symmetrically for $\mathrm{red}_2$, the strictly-second-type part and $R_2$) together with the two cusp laws `CuspLawInfty` and `CuspLawZero`; `hO`, the order law at fixed places, that for such $f$ and every $\delta$-fixed affine place $v$ the pushforward along $\mathrm{red}_1$ of the divisor of $f$ at $v$ equals $\operatorname{ord}_v$ of the $R_1$-residue plus $\operatorname{ord}_{\delta(\varphi v)}$ of the $R_2$-residue; `hRL`, the regularity law relative to $SS$, in two clauses bounding the residues below by $0$ at $\delta$-fixed affine places and producing a common value of the two residues at each node pair of $SS$, under the respective non-negativity hypotheses on $\operatorname{ord}_V f$; and `hNV`, the node value law relative to $SS$, producing for each node pair a nonzero common value of the two residues whenever no place $V$ with $\operatorname{ord}_V f \neq 0$ reduces to that pair. Here a place $v$ of $\bar F$ is affine (`IsAffinePlace`) when the element of $\bar F$ with $q$-expansion `jqModC κ` has a value in $\kappa$ at $v$.
--
--   The normalisations pinning $\alpha$, $\beta$ and $\theta$ are: `hα_coe`, that $\alpha$ is the inclusion on $q$-expansions; `hβ_coe`, that the $q$-expansion of $\beta u$ is obtained from that of $u$ by `qExpand (AlgebraicClosure ℚ) p`, i.e. substitution of $q^p$ for $q$; `hθgal`, that $\theta$ commutes with the arithmetic Galois action `arithmeticGalois` of $\operatorname{Aut}(\overline{\mathbb{Q}}/\mathbb{Q})$ on $F_M$; and `hβθ`, that $\beta$ is $\alpha$ followed by $\theta$.
--
--   Two further local hypotheses `hLFst` and `hLSnd` are imposed, in mirror-image form. In `hLFst`: whenever $Q$ and $Q'$ are distinct places of $F_M$ of strictly first type with $\mathrm{red}_1 Q' = \mathrm{red}_1 Q$ and this common image an affine place of $\bar F$; whenever $n$ is a natural number with $n \neq 0$ in $\kappa$; whenever $g \in R_1$ has nonzero $R_1$-residue, $\operatorname{ord}_Q g = -n$, $\operatorname{ord}_{Q'} g = n$ and $\operatorname{ord}_W g = 0$ for every strictly-first-type place $W$ other than $Q, Q'$ with $\mathrm{red}_1 W = \mathrm{red}_1 Q$; and whenever $e \in A$ and $\varepsilon \in R_1$ has nonzero $R_1$-residue and $g = 1 + e\varepsilon$; then $-1 \le \operatorname{ord}_{\mathrm{red}_1 Q}$ of the $R_1$-residue of $\varepsilon$. The hypothesis `hLSnd` is the same statement with strictly second type, $\mathrm{red}_2$ and $R_2$ in place of strictly first type, $\mathrm{red}_1$ and $R_1$.
--
--   The unit hypothesis `hUnit` asserts the existence of $u_1, u_2 \in F_M$ and divisors $D_1, D_2$ of $F_M$ with $D_i(W) = \operatorname{ord}_W u_i$ for all $W$, such that: $u_1$ lies in $R_1$ with nonzero residue and $u_1^{-1}$ also lies in $R_1$, for every non-$\delta$-fixed place $v$ of $\bar F$ the pushforward along $\mathrm{red}_1$ of the strictly-first-type part of $D_1$ at $v$ equals $\operatorname{ord}_v$ of the $R_1$-residue of $u_1$, and for every place $C$ of $F_M$ on the infinity side (`IsInftySide`, i.e. $C$ is cuspidal for $j$ and the quotient of the $q^p$-expansion of $j$ by the $p$-th power of $j$ has at $C$ a value lifting $1$) the pushforward along $\mathrm{red}_1$ of the restriction of $D_1$ to infinity-side places, evaluated at $\mathrm{red}_1 C$, equals $\operatorname{ord}_{\mathrm{red}_1 C}$ of the $R_1$-residue of $u_1$; every nonzero $f \in F_M$ admits $m \neq 0$ and $j \in \mathbb{Z}$ with $f^m u_1^{j}$ in $R_2$ with nonzero $R_2$-residue; the mirror-image clauses hold for $u_2$ with $R_2$, $\mathrm{red}_2$, the strictly-second-type part of $D_2$ and the zero-side places (`IsZeroSide`); and every nonzero $f \in F_M$ admits $m \neq 0$ and $j \in \mathbb{Z}$ with $f^m u_2^{j}$ in $R_1$ with nonzero $R_1$-residue.
--
--   The cusp-fibre hypothesis `hcusp` asserts that every non-affine place $w$ of $\bar F$ is of the form $\mathrm{red}_1 C$ for some infinity-side place $C$ and also of the form $\mathrm{red}_2 C$ for some zero-side place $C$. The orientation hypotheses are `horientInf`, that $\delta(\varphi(\mathrm{red}_1 C)) = \mathrm{red}_2 C$ for every infinity-side place $C$, and `horient0`, that $\mathrm{red}_1 C = \varphi(\mathrm{red}_2 C)$ for every zero-side place $C$.
--
--   Under all of these hypotheses the conclusion is: for every finite set $S$ of elements of $\kappa$ such that no $s \in S$ belongs to `ssJSet p κ` — the set of those $j \in \kappa$ for which every elliptic Weierstrass curve over $\kappa$ with $j$-invariant $j$ has only the zero point killed by $p$ — and for every class $x \in J_H(M) = \mathrm{Pic}^0$ of $F_M$ over $\overline{\mathbb{Q}}$, there exists a degree-zero divisor $E$ of $F_M$ such that $E$ represents $x$, i.e. `Pic0.mk E = x`, and such that for every place $V$ in the support of $E$ and every $xj \in F_M$ whose $q$-expansion is `jqModC (AlgebraicClosure ℚ)` there exists $a \in A$ with $\operatorname{ord}_V(xj - a) > 0$ and with the residue of $a$ in $\kappa$ not lying in $S$.
--
--   This is a moving lemma for divisor classes on $X_H(M)$ at a place above $p$: every class in $J_H(M)$ has a degree-zero representative all of whose support places are non-cuspidal with $j$-value specialising outside a prescribed finite set of non-supersingular residues, the set $S$ being chosen to avoid bad reductions in the level-lowering argument. It is obtained from the corresponding one-place surgery statement for the same kit of laws together with the general divisor-surgery principle [`AlgebraicCurve.Divisor.exists_isPrincipal_degree_eq_zero_forall_mem_support_add_of_surgery`](thm.html#AlgebraicCurve.Divisor.exists_isPrincipal_degree_eq_zero_forall_mem_support_add_of_surgery), and is used in turn by the refinement that in addition separates the reductions of the support places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHPlaceSpecialization_exists_rep_forall_exists_ord_sub_pos_residue_notMem_of_isModel_of_regularityLaw_of_orderLawFixed_of_coe_of_unit_of_cusp_of_orient.lean

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_AlgebraicCurve_AdelicIndex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing
open ModularCurve
open scoped MatrixGroups Classical

theorem ModularCurve.JHPlaceSpecialization.exists_rep_forall_exists_ord_sub_pos_residue_notMem_of_isModel_of_regularityLaw_of_orderLawFixed_of_coe_of_unit_of_cusp_of_orient
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
    (hFix : {v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) | JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v}.Finite)
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
    (hcusp : ∀ w : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)),
      ¬ (JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A)) w →
        (∃ C, (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A)) C ∧ Psp.reduceFst α hα C = w) ∧
        (∃ C, (JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A)) C ∧ Psp.reduceSnd β hβ δ C = w))

    (horientInf : ∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A) C →
      δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (Psp.reduceFst α hα C)) = Psp.reduceSnd β hβ δ C)
    (horient0 : ∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A) C →
      Psp.reduceFst α hα C = qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (Psp.reduceSnd β hβ δ C))
 :
    ∀ (S : Finset (ResidueField ↥A)),
      (∀ s ∈ S, s ∉ @ssJSet p (ResidueField ↥A) _ (Classical.decEq _)) →
      ∀ x : JH M H,
        ∃ (E : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)))),
          Pic0.mk E = x ∧
            ∀ V ∈ (E : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)).support,
              ∀ (xj : ↥(xHFunctionFieldBar M H)), ((xj : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ) →
                ∃ a : ↥A, 0 < V.ord (xj - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a : AlgebraicClosure ℚ)) ∧
                  IsLocalRing.residue ↥A a ∉ S := by sorry
