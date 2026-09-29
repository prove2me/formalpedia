-- Prove2me | Theorems.Thm_ModularCurve_JHPlaceSpecialization_ProlongationDatum_exists_sub_algebraMap_forall_ord_pos_reduceFst_notMem_of_fixed_of_isAffinePlace
-- name    : ModularCurve.JHPlaceSpecialization.ProlongationDatum.exists_sub_algebraMap_forall_ord_pos_reduceFst_notMem_of_fixed_of_isAffinePlace
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/d95dedcd-e335-5be0-9607-8b9540d13525
-- title:
--   Constant shift at a fixed affine pole avoiding a bad set
-- statement:
--   Throughout, $p$ is a prime and $M$ a non-zero level with $p \mid M$ (`hpM`) and $p^2 \nmid M$ (`hpM2`), $H$ is a subgroup of $(\mathbb Z/M)^\times$ satisfying `hHp`: every unit $u$ of $\mathbb Z/M$ whose image under `ZMod.unitsMap` for $M/p \mid M$ is $1$ lies in $H$. Further, $A$ is a valuation subring of $\overline{\mathbb Q}$ with $p$ a non-unit of $A$ (`hA`, i.e. `A.LiesOverPrime p`), whose residue field $\kappa =$ `ResidueField ↥A` is of characteristic $p$ and algebraically closed. Write $F_M$ for `xHFunctionFieldBar M H`, the base change to $\overline{\mathbb Q}$ of the function field of $X_H(M)$ inside $\overline{\mathbb Q}$-Laurent series, $F_{M/p}$ for `xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)`, where `infSubgroup` is the image of $H$ in $(\mathbb Z/(M/p))^\times$, and $\bar F$ for `JHNeronObjectAtP.Fbar p M H hpM κ`, the $q$-expansion function field over $\kappa$ for the group `ΓN p M H hpM`. Places are in the sense of the project's `Place` (valuation subrings containing the base field, proper, with principal maximal ideal), and `ord` is the associated normalised integer order function; $\varphi$ denotes `qExpFrobeniusPlaceModL κ (ΓN p M H hpM) p`, the pullback of places along the mod $p$ Frobenius of $\bar F$.
--
--   The data are: an automorphism $\theta$ of $F_M$ over $\overline{\mathbb Q}$; two integral $\overline{\mathbb Q}$-algebra maps $\alpha, \beta : F_{M/p} \to F_M$ with integrality witnesses `hα`, `hβ`; a unit $pb$ of $\mathbb Z/(M/p)$ whose underlying residue is $p$ (`hpb`); a self-map $\delta$ of the places of $\bar F$ over $\kappa$ which by `hδ` is the action on places of the semilinear automorphism attached to the diamond operator `diamondActionModL κ (M/p) (infSubgroup p M H hpM)` evaluated at [`CuspForm.gammaLift (M / p) pb`](def/CuspForm_HeckeOperatorFormsGammaH.html#L36); a finite set $SS$ of pairs of places of $\bar F$ which by `hSS` is exactly `ssNodePairsQExp κ (ΓN p M H hpM) p`, the set of pairs $s$ with $s_2$ supersingular and $s_1 = \varphi(s_2)$; a place-specialisation datum `Psp : JHPlaceSpecialization p M H hpM A`, consisting of a map `sp` from places of $F_{M/p}$ to places of $\bar F$ together with a map on degree-zero divisor classes and the compatibility axioms of that structure ($q$-expansion compatibility of divisors, surjectivity, realisation of pushed-forward divisors, invariance under the inertia subgroup, Frobenius equivariance, and compatibility on $\mathrm{Pic}^0$); and a prolongation datum `Rpd : Rpd.ProlongationDatum Psp θ`, i.e. two regular prolongations $R_1, R_2$ of $A$ from $\overline{\mathbb Q}$ to $F_M$ with residue maps to $\bar F$, such that Laurent series with coefficients in $A$ are $R_1$-integral with residue the coefficientwise reduction, and $R_2$-integrality and $R_2$-residues are transported from $R_1$ along $\theta$.
--
--   For a place $W$ of $F_M$ set $\mathrm{red}_1 W = \mathrm{sp}(W|_\alpha)$ and $\mathrm{red}_2 W = \delta(\mathrm{sp}(W|_\beta))$ (`reduceFst`, `reduceSnd`), and call a place $v$ of $\bar F$ fixed if $\varphi(\delta(\varphi v)) = v$ (`Fixed`) and affine if some $x \in \bar F$ with Laurent expansion `jqModC κ` has a value in $\kappa$ at $v$ (`IsAffinePlace`). $W$ is of strict first type when $\delta(\varphi(\mathrm{red}_1 W)) = \mathrm{red}_2 W$ and $\mathrm{red}_1 W$ is not fixed, and of strict second type when $\mathrm{red}_1 W = \varphi(\mathrm{red}_2 W)$ and $\mathrm{red}_2 W$ is not fixed.
--
--   The structural hypotheses are the following groups. `hTD` (type dichotomy): every place $W$ of $F_M$ satisfies $\mathrm{red}_1 W = \varphi(\mathrm{red}_2 W)$ or $\delta(\varphi(\mathrm{red}_1 W)) = \mathrm{red}_2 W$. `hFix`: the set of fixed places is finite. `hmodel` (`IsModel`, four laws): for $f$ integral for both prolongations with non-zero residues $\bar f_1, \bar f_2$ and $D$ the divisor of $f$, the pushforward under $\mathrm{red}_1$ of the strict-first-type part of $D$ computes $\mathrm{ord}_v \bar f_1$ at every non-fixed $v$, the pushforward under $\mathrm{red}_2$ of the strict-second-type part computes $\mathrm{ord}_v \bar f_2$ at every non-fixed $v$, and the analogous identities hold for the parts of $D$ supported on infinity-side, respectively zero-side, cuspidal places. `hO` (`OrderLawFixed`): in the same situation, at a fixed affine place $v$ the pushforward of the whole divisor equals $\mathrm{ord}_v \bar f_1 + \mathrm{ord}_{\delta(\varphi v)} \bar f_2$. `hRL` (`RegularityLaw`, two clauses): if $f$ is integral for both prolongations and has no pole among places reducing to a fixed affine $v$ under $\mathrm{red}_1$, then the residues are regular at $v$ and at $\delta(\varphi v)$ respectively; and for $s \in SS$ with no pole among places with $\mathrm{red}_1$-image $s_1$, the two residues take a common value at $s_1$ and $s_2$. `hNV` (`NodeValueLaw`): for $f$ with non-zero residues and $s \in SS$ such that no place $V$ with $\mathrm{ord}_V f \neq 0$ has $(\mathrm{red}_1 V, \mathrm{red}_2 V) = s$, the two residues take a common non-zero value at $s_1$ and $s_2$. `hα_coe` and `hβ_coe`: $\alpha$ is the identity on underlying Laurent series, and $\beta$ is the substitution $q \mapsto q^p$ (`qExpand`). `hθgal`: $\theta$ commutes with the arithmetic Galois action of $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ on $F_M$. `hβθ`: $\beta$ equals $\alpha$ followed by $\theta$.
--
--   Two further local hypotheses, `hLFst` and `hLSnd`, are of the following shape (stated for the first, with the second obtained by replacing strict first type, $\mathrm{red}_1$ and $R_1$ by strict second type, $\mathrm{red}_2$ and $R_2$): if $Q \neq Q'$ are strict-first-type places of $F_M$ with equal and affine $\mathrm{red}_1$-image, $n$ a natural number non-zero in $\kappa$, $g$ an $R_1$-integral element with non-zero residue having $\mathrm{ord}_Q g = -n$, $\mathrm{ord}_{Q'} g = n$ and $\mathrm{ord}_W g = 0$ for every other strict-first-type $W$ with the same $\mathrm{red}_1$-image, and $g = 1 + e\varepsilon$ with $e \in A$ and $\varepsilon$ an $R_1$-integral element with non-zero residue, then $-1 \le \mathrm{ord}_{\mathrm{red}_1 Q}$ of the $R_1$-residue of $\varepsilon$.
--
--   The hypothesis `hUnit` asserts the existence of $u_1, u_2 \in F_M$ and divisors $D_1, D_2$ equal to the divisors of $u_1$ and of $u_2$, such that: $u_1$ and $u_1^{-1}$ are $R_1$-integral with non-zero $R_1$-residue, the pushforward under $\mathrm{red}_1$ of the strict-first-type part of $D_1$ computes the order of that residue at every non-fixed place, and the pushforward of the infinity-side part of $D_1$ computes it at the $\mathrm{red}_1$-image of every infinity-side place; every non-zero $f \in F_M$ admits $m \neq 0$ and $j \in \mathbb Z$ with $f^m u_1^{\,j}$ $R_2$-integral of non-zero $R_2$-residue; and symmetrically for $u_2$ with $R_2$, $\mathrm{red}_2$, the strict-second-type and zero-side parts of $D_2$, together with the existence, for every non-zero $f$, of $m \neq 0$ and $j$ with $f^m u_2^{\,j}$ $R_1$-integral of non-zero $R_1$-residue. The hypothesis `hcusp` states that every non-affine place $w$ of $\bar F$ is the $\mathrm{red}_1$-image of some infinity-side place and the $\mathrm{red}_2$-image of some zero-side place. The orientation hypotheses are `horientInf`: $\delta(\varphi(\mathrm{red}_1 C)) = \mathrm{red}_2 C$ for every infinity-side place $C$, and `horient0`: $\mathrm{red}_1 C = \varphi(\mathrm{red}_2 C)$ for every zero-side place $C$.
--
--   Finally, $B$ is a finite set of places of $\bar F$ over $\kappa$, and $V_0$ is a place of $F_M$ whose reduction $\mathrm{red}_1 V_0$ is fixed (`hfix`), is affine (`haff`) and differs from both coordinates of every pair in $SS$ (`hord`); and $g \in F_M$ is integral for $R_1$ and for $R_2$ (witnesses $h_1, h_2$) with non-zero residues $\bar g_1, \bar g_2$ (`hg₁`, `hg₂`), with $\mathrm{ord}_{V_0} g = -1$ (`hpole`), such that every place $V \neq V_0$ with $\mathrm{ord}_V g < 0$ has both $\mathrm{red}_1 V \notin B$ and $\mathrm{red}_2 V \notin B$ (`hother`), and such that (`hres`) either $\mathrm{ord}_{\mathrm{red}_1 V_0} \bar g_1 = -1$ and $\mathrm{ord}_{\delta(\varphi(\mathrm{red}_1 V_0))} \bar g_2 = 0$, or $\mathrm{ord}_{\mathrm{red}_1 V_0} \bar g_1 = 0$ and $\mathrm{ord}_{\delta(\varphi(\mathrm{red}_1 V_0))} \bar g_2 = -1$.
--
--   The conclusion is that there exists $c \in A$ such that, writing $g - c$ for $g$ minus the image of $c$ under $\overline{\mathbb Q} \to F_M$: $g - c$ is integral for $R_1$ and for $R_2$; its $R_1$-residue and its $R_2$-residue are both non-zero; $\mathrm{ord}_{V_0}(g - c) = -1$; every place $V$ with $\mathrm{ord}_V(g-c) < 0$ satisfies $\mathrm{ord}_V g < 0$; every place $V \neq V_0$ with $\mathrm{ord}_V(g-c) > 0$ satisfies $\mathrm{red}_1 V \notin B$; and there is a divisor $q$ of $F_M$ over $\overline{\mathbb Q}$ with $q(V) = \mathrm{ord}_V(g-c)$ for every place $V$ and $\deg q = 0$.
--
--   This is the collision-place form of the constant-shift step in the avoidance argument on the special fibre of $X_H(M)$ at a prime $p$ exactly dividing $M$: a function with a simple pole at a place whose first reduction is a fixed affine place is modified by an additive constant from $A$ so that its new zeros, apart from $V_0$, reduce outside a prescribed finite set of bad places, while integrality, non-vanishing of both residues and the pole at $V_0$ are preserved. It is used by [`ModularCurve.JHPlaceSpecialization.exists_isPrincipal_apply_eq_neg_one_forall_support_good_of_fixed_of_isAffinePlace`](thm.html#ModularCurve.JHPlaceSpecialization.exists_isPrincipal_apply_eq_neg_one_forall_support_good_of_fixed_of_isAffinePlace), which produces principal divisors with controlled support in the specialisation argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHPlaceSpecialization_ProlongationDatum_exists_sub_algebraMap_forall_ord_pos_reduceFst_notMem_of_fixed_of_isAffinePlace.lean

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

theorem ModularCurve.JHPlaceSpecialization.ProlongationDatum.exists_sub_algebraMap_forall_ord_pos_reduceFst_notMem_of_fixed_of_isAffinePlace
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

    (B : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (V₀ : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (hfix : JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ (Psp.reduceFst α hα V₀))
    (haff : JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A) (Psp.reduceFst α hα V₀))
    (hord : ∀ s ∈ SS, Psp.reduceFst α hα V₀ ≠ s.1 ∧ Psp.reduceFst α hα V₀ ≠ s.2)

    (g : ↥(xHFunctionFieldBar M H)) (h₁ : g ∈ Rpd.R₁.integers) (h₂ : g ∈ Rpd.R₂.integers)
    (hg₁ : Rpd.R₁.residue ⟨g, h₁⟩ ≠ 0) (hg₂ : Rpd.R₂.residue ⟨g, h₂⟩ ≠ 0)
    (hpole : V₀.ord g = -1)
    (hother : ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), V ≠ V₀ → V.ord g < 0 → Psp.reduceFst α hα V ∉ B ∧ Psp.reduceSnd β hβ δ V ∉ B)
    (hres : ((Psp.reduceFst α hα V₀).ord (Rpd.R₁.residue ⟨g, h₁⟩) = -1 ∧
        (δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (Psp.reduceFst α hα V₀))).ord (Rpd.R₂.residue ⟨g, h₂⟩) = 0) ∨
      ((Psp.reduceFst α hα V₀).ord (Rpd.R₁.residue ⟨g, h₁⟩) = 0 ∧
        (δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (Psp.reduceFst α hα V₀))).ord (Rpd.R₂.residue ⟨g, h₂⟩) = -1)) :
    ∃ (c : ↥A) (h₁' : g - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (c : AlgebraicClosure ℚ) ∈ Rpd.R₁.integers) (h₂' : g - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (c : AlgebraicClosure ℚ) ∈ Rpd.R₂.integers),
      Rpd.R₁.residue ⟨g - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (c : AlgebraicClosure ℚ), h₁'⟩ ≠ 0 ∧ Rpd.R₂.residue ⟨g - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (c : AlgebraicClosure ℚ), h₂'⟩ ≠ 0 ∧
      V₀.ord (g - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (c : AlgebraicClosure ℚ)) = -1 ∧
      (∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), V.ord (g - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (c : AlgebraicClosure ℚ)) < 0 → V.ord g < 0) ∧
      (∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), V ≠ V₀ → 0 < V.ord (g - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (c : AlgebraicClosure ℚ)) → Psp.reduceFst α hα V ∉ B) ∧
      ∃ q : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), (∀ V, q V = V.ord (g - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (c : AlgebraicClosure ℚ))) ∧ Divisor.degree q = 0 := by sorry
