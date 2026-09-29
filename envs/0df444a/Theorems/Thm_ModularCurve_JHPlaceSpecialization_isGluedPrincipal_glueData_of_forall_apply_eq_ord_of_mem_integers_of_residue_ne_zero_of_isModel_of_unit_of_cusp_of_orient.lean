-- Prove2me | Theorems.Thm_ModularCurve_JHPlaceSpecialization_isGluedPrincipal_glueData_of_forall_apply_eq_ord_of_mem_integers_of_residue_ne_zero_of_isModel_of_unit_of_cusp_of_orient
-- name    : ModularCurve.JHPlaceSpecialization.isGluedPrincipal_glueData_of_forall_apply_eq_ord_of_mem_integers_of_residue_ne_zero_of_isModel_of_unit_of_cusp_of_orient
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/1f80f28d-fc38-561e-92eb-b34cdf128854
-- title:
--   Glued principality of the gluing datum of a common unit
-- statement:
--   Fix a prime $p$ and a modulus $M$ with $p \mid M$ and $p^2 \nmid M$, and a subgroup $H \le (\mathbb Z/M)^\times$ containing the kernel of the reduction $(\mathbb Z/M)^\times \to (\mathbb Z/(M/p))^\times$ (the hypothesis `hHp`: every unit $u$ with `ZMod.unitsMap` $u = 1$ lies in $H$). Fix a valuation subring $A$ of $\overline{\mathbb Q}$ lying over $p$ (`LiesOverPrime`, i.e. $p$ is a non-unit of $A$) whose residue field $\kappa$ has characteristic $p$ and is algebraically closed. Write $F_M =$ `xHFunctionFieldBar M H` for the base change to $\overline{\mathbb Q}$ of the function field of $X_H(M)$ inside Laurent series, $F_{M/p} =$ `xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)` for the corresponding field at level $M/p$ with the image subgroup `infSubgroup`, $\bar F =$ `JHNeronObjectAtP.Fbar p M H hpM` $\kappa$ for the characteristic-$p$ $q$-expansion function field at level `JHNeronObjectAtP.ΓN p M H hpM`, and $\Phi =$ `qExpFrobeniusPlaceModL` $\kappa$ `(JHNeronObjectAtP.ΓN p M H hpM)` $p$ for the Frobenius operation on places of $\bar F$ over $\kappa$.
--
--   The degeneracy data consist of: a $\overline{\mathbb Q}$-algebra automorphism $\theta$ of $F_M$; two integral $\overline{\mathbb Q}$-algebra maps $\alpha, \beta : F_{M/p} \to F_M$ (integrality being `hα`, `hβ`); a unit $pb$ of $\mathbb Z/(M/p)$ whose underlying residue is $p$; and a self-map $\delta$ of the places of $\bar F$ over $\kappa$ which, by `hδ`, is the action of the diamond automorphism `diamondActionModL` $\kappa$ $(M/p)$ `(infSubgroup p M H hpM)` applied to [`CuspForm.gammaLift (M / p) pb`](def/CuspForm_HeckeOperatorFormsGammaH.html#L36), viewed as a semilinear automorphism through `SemilinearAut.ofAlgAut`. Further, $SS$ is a finite set of pairs of places of $\bar F$ over $\kappa$, characterised by `hSS` as consisting exactly of the members of `ssNodePairsQExp`, that is, of the pairs $s$ with $s_2 \in$ `ssPlacesQExp (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p` and $s_1 = \Phi(s_2)$.
--
--   The specialisation data are a term $Psp$ of `JHPlaceSpecialization p M H hpM A` (a specialisation map $sp$ from places of $F_{M/p}$ to places of $\bar F$ together with its divisor-pushforward, surjectivity, inertia and Frobenius clauses and its $\mathrm{Pic}^0$-compatibility) and a term $Rpd$ of `JHPlaceSpecialization.ProlongationDatum Psp θ`, consisting of two regular prolongations $R_1, R_2$ of $A$ to $F_M$ with residues in $\bar F$, the $q$-expansion clause for $R_1$, and the identifications $f \in R_2$`.integers` $\iff \theta f \in R_1$`.integers` with matching residues. For a place $W$ of $F_M$ put $\mathrm{red}_1(W) = sp(W|_\alpha)$ and $\mathrm{red}_2(W) = \delta(sp(W|_\beta))$, where $W|_\alpha$, $W|_\beta$ denote the restrictions along $\alpha$, $\beta$; $W$ is of strict first type (`IsStrictFst`) when $\delta(\Phi(\mathrm{red}_1 W)) = \mathrm{red}_2 W$ and $\mathrm{red}_1 W$ is not $\delta$-fixed, and of strict second type (`IsStrictSnd`) when $\mathrm{red}_1 W = \Phi(\mathrm{red}_2 W)$ and $\mathrm{red}_2 W$ is not $\delta$-fixed; here a place $v$ of $\bar F$ is $\delta$-fixed (`Fixed`) when $\Phi(\delta(\Phi v)) = v$, and is affine (`IsAffinePlace`) when some element of $\bar F$ with $q$-expansion the modular $j$-function has a value at $v$.
--
--   The structural hypotheses are: `hTD`, the type dichotomy, asserting that every place $W$ of $F_M$ satisfies $\mathrm{red}_1 W = \Phi(\mathrm{red}_2 W)$ or $\delta(\Phi(\mathrm{red}_1 W)) = \mathrm{red}_2 W$; `hFix`, finiteness of the set of $\delta$-fixed places; `hmodel`, that $Rpd$ `IsModel` for $(\alpha,\beta,\delta)$, i.e. the conjunction of `DivisorLawFst` and `DivisorLawSnd` (for $f$ lying in both integer rings with both residues non-zero and $D$ the divisor of $f$, the pushforward along $\mathrm{red}_1$ of the strict-first part of $D$ computes the order of the $R_1$-residue of $f$ at every non-fixed place, and symmetrically along $\mathrm{red}_2$ for the strict-second part and the $R_2$-residue) together with the cusp laws `CuspLawInfty` for $\alpha$ and `CuspLawZero` for $\beta, \delta$; `hO`, the `OrderLawFixed`, asserting that for such $f$ and $D$ and every $\delta$-fixed affine place $v$ one has $(\mathrm{red}_{1*}D)(v) = v.\mathrm{ord}(\bar f^{R_1}) + (\delta(\Phi v)).\mathrm{ord}(\bar f^{R_2})$; `hRL`, the `RegularityLaw` for $SS$, whose two clauses assert, for $f$ in both integer rings, first that if $v$ is $\delta$-fixed and affine and $\mathrm{ord}_V f \ge 0$ for all $V$ with $\mathrm{red}_1 V = v$, then $v.\mathrm{ord}(\bar f^{R_1}) \ge 0$ whenever $\bar f^{R_1} \neq 0$ and $(\delta(\Phi v)).\mathrm{ord}(\bar f^{R_2}) \ge 0$ whenever $\bar f^{R_2} \neq 0$, and second that for $s \in SS$ with $\mathrm{ord}_V f \ge 0$ for all $V$ with $\mathrm{red}_1 V = s_1$ there is a common value $c \in \kappa$ of $\bar f^{R_1}$ at $s_1$ and of $\bar f^{R_2}$ at $s_2$; and `hNV`, the `NodeValueLaw` for $SS$, asserting that for $f$ in both integer rings with non-zero residues and $s \in SS$ such that no place $V$ with $\mathrm{ord}_V f \neq 0$ satisfies both $\mathrm{red}_1 V = s_1$ and $\mathrm{red}_2 V = s_2$, there is a non-zero $c \in \kappa$ which is simultaneously a value of $\bar f^{R_1}$ at $s_1$ and of $\bar f^{R_2}$ at $s_2$.
--
--   The compatibility hypotheses are: `hα_coe`, that $\alpha$ is the identity on $q$-expansions; `hβ_coe`, that $\beta$ acts on $q$-expansions by `qExpand` $\overline{\mathbb Q}$ $p$, i.e. $q \mapsto q^p$; `hθgal`, that $\theta$ commutes with the action of every $\sigma \in \mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ through `arithmeticGalois`; and `hβθ`, that $\beta$ is $\alpha$ followed by $\theta$.
--
--   The two local hypotheses `hLFst` and `hLSnd` are mirror-image statements on the first and second side. `hLFst` requires: for places $Q \neq Q'$ of $F_M$, both of strict first type, with $\mathrm{red}_1 Q' = \mathrm{red}_1 Q$ and $\mathrm{red}_1 Q$ affine; for a natural number $n$ whose image in $\kappa$ is non-zero; for $g$ in $R_1$`.integers` with non-zero $R_1$-residue such that $\mathrm{ord}_Q g = -n$, $\mathrm{ord}_{Q'} g = n$ and $\mathrm{ord}_W g = 0$ for every further place $W$ of strict first type with $\mathrm{red}_1 W = \mathrm{red}_1 Q$; and for $e \in A$ and $\varepsilon$ in $R_1$`.integers` with non-zero $R_1$-residue such that $g = 1 + e\,\varepsilon$, the inequality $(\mathrm{red}_1 Q).\mathrm{ord}(\bar\varepsilon^{R_1}) \ge -1$. `hLSnd` is the same statement with `IsStrictSnd`, $\mathrm{red}_2$, $R_2$ throughout.
--
--   The unit hypothesis `hUnit` posits elements $u_1, u_2$ of $F_M$ and divisors $D_1, D_2$ with $D_i$ the divisor of $u_i$, such that: $u_1$ and $u_1^{-1}$ lie in $R_1$`.integers` with $\bar u_1^{R_1} \neq 0$, the pushforward along $\mathrm{red}_1$ of the strict-first part of $D_1$ computes $v.\mathrm{ord}(\bar u_1^{R_1})$ at every non-fixed place $v$, and for every place $C$ of $F_M$ on the infinity side (`IsInftySide`) the pushforward along $\mathrm{red}_1$ of the restriction of $D_1$ to the infinity-side places takes at $\mathrm{red}_1 C$ the value $(\mathrm{red}_1 C).\mathrm{ord}(\bar u_1^{R_1})$; every non-zero $f$ admits $m \neq 0$ and $j \in \mathbb Z$ with $f^m u_1^{\,j}$ in $R_2$`.integers` of non-zero residue; and symmetrically for $u_2$, $D_2$, $R_2$, $\mathrm{red}_2$ and the zero-side places (`IsZeroSide`), together with the existence, for every non-zero $f$, of $m \neq 0$ and $j$ with $f^m u_2^{\,j}$ in $R_1$`.integers` of non-zero residue.
--
--   Finally, `hcusp` requires that every non-affine place $w$ of $\bar F$ be both of the form $\mathrm{red}_1 C$ for some infinity-side place $C$ and of the form $\mathrm{red}_2 C$ for some zero-side place $C$; `horientInf` requires $\delta(\Phi(\mathrm{red}_1 C)) = \mathrm{red}_2 C$ for infinity-side $C$, and `horient0` requires $\mathrm{red}_1 C = \Phi(\mathrm{red}_2 C)$ for zero-side $C$; and $SS$ is non-empty (`hSSne`).
--
--   The function to be treated is a non-zero $f \in F_M$ lying in both $R_1$`.integers` and $R_2$`.integers` with both residues $\bar f^{R_1}, \bar f^{R_2}$ non-zero, $D$ is the divisor of $f$ (i.e. $D(V) = \mathrm{ord}_V f$ for all $V$), $D$ is good (`IsGoodDiv`: every place in the support of $D$ is of strict first or of strict second type), and the gluing datum $x =$ `glueData` $= \bigl(\mathrm{red}_{1*}(D|_{\text{strict first}}),\ \mathrm{red}_{2*}(D|_{\text{strict second}}),\ 0\bigr)$ is admissible, that is, both divisor components have degree zero and, for every $s \in SS$, the first component vanishes at $s_1$ and the second at $s_2$.
--
--   Under these hypotheses the gluing datum $x$ is glued principal: there exist non-zero $g_1, g_2 \in \bar F$ and maps $a, b : SS \to \kappa^\times$ such that (i) for every place $v$ of $\bar F$ over $\kappa$, the pushforward $\mathrm{red}_{1*}(D|_{\text{strict first}})$ takes at $v$ the value $v.\mathrm{ord}(g_1)$; (ii) for every such $v$, the pushforward $\mathrm{red}_{2*}(D|_{\text{strict second}})$ takes at $v$ the value $v.\mathrm{ord}(g_2)$; (iii) for every $s \in SS$, $g_1$ has value $a(s)$ at $s_1$ and $g_2$ has value $b(s)$ at $s_2$, in the sense of `HasValue`, namely $g_1$ lies in the valuation ring of $s_1$ with residue the image of $a(s)$ in the residue field of $s_1$, and likewise for $g_2$ at $s_2$; and (iv) the third component of $x$, which is the zero function, equals $s \mapsto$ `Additive.ofMul` $(a(s)/b(s))$, so that $a(s) = b(s)$ for every $s \in SS$.
--
--   This is the principality step in the analysis of the special fibre at $p \,\|\, M$ of the Jacobian of $X_H(M)$, where that fibre is described by divisors on two copies of the level-$(M/p)$ curve over $\kappa$ glued at the supersingular node pairs $SS$: it shows that the gluing datum attached to the divisor of a function $f$ integral with non-zero residue for both prolongations $R_1, R_2$ is principal in the glued sense. It is one of the two inputs to the corresponding statement in which the common-integrality hypotheses on $f$ are removed, the other being the normalisation of an arbitrary function by a modular unit.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHPlaceSpecialization_isGluedPrincipal_glueData_of_forall_apply_eq_ord_of_mem_integers_of_residue_ne_zero_of_isModel_of_unit_of_cusp_of_orient.lean

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_ComponentGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JHNeronObjectAtP
open scoped MatrixGroups

open Classical in

theorem ModularCurve.JHPlaceSpecialization.isGluedPrincipal_glueData_of_forall_apply_eq_ord_of_mem_integers_of_residue_ne_zero_of_isModel_of_unit_of_cusp_of_orient
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
    (hSSne : SS.Nonempty)
    (f : ↥(xHFunctionFieldBar M H)) (hf : f ≠ 0)
    (h₁ : f ∈ Rpd.R₁.integers) (h₂ : f ∈ Rpd.R₂.integers) (hr₁ : Rpd.R₁.residue ⟨f, h₁⟩ ≠ 0) (hr₂ : Rpd.R₂.residue ⟨f, h₂⟩ ≠ 0)
    (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (hDf : ∀ V, D V = V.ord f)
    (hgood : Psp.IsGoodDiv α β hα hβ δ D)
    (hadm : Psp.glueData α β hα hβ δ SS D ∈ GluingData.admissible SS) :
    GluingData.IsGluedPrincipal SS (Psp.glueData α β hα hβ δ SS D) := by sorry
