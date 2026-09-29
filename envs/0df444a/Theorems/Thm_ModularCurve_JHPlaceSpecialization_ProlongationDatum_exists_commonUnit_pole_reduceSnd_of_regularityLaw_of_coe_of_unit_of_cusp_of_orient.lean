-- Prove2me | Theorems.Thm_ModularCurve_JHPlaceSpecialization_ProlongationDatum_exists_commonUnit_pole_reduceSnd_of_regularityLaw_of_coe_of_unit_of_cusp_of_orient
-- name    : ModularCurve.JHPlaceSpecialization.ProlongationDatum.exists_commonUnit_pole_reduceSnd_of_regularityLaw_of_coe_of_unit_of_cusp_of_orient
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/dc2cef2a-ee40-5576-8963-9743ef473765
-- title:
--   Common unit with prescribed simple pole on the second sheet
-- statement:
--   Throughout, $\bar{\mathbb Q}$ denotes `AlgebraicClosure ℚ`, $F_M$ the field $\mathtt{xHFunctionFieldBar}\,M\,H$ (the base change to $\bar{\mathbb Q}$ of the $q$-expansion function field of $X_H$ inside $\mathbb Q$-Laurent series), $F_{M/p}$ the corresponding field for level $M/p$ and the subgroup $\mathtt{infSubgroup}\,p\,M\,H =$ image of $H$ in $(\mathbb Z/(M/p))^\times$, and, for a field $\kappa$, $\bar F$ the characteristic-$\kappa$ $q$-expansion function field $\mathtt{JHNeronObjectAtP.Fbar}\,p\,M\,H\,hpM\,\kappa$. A place of a field extension is a valuation subring containing the base field, distinct from the whole field and a principal ideal ring, and $\mathrm{ord}_V$ is the associated normalised additive valuation. Write $\varphi = \mathtt{qExpFrobeniusPlaceModL}$, the operation of restricting a place along the $q$-expansion Frobenius.
--
--   *Arithmetic data.* A prime $p$ and a nonzero level $M$ with a subgroup $H \le (\mathbb Z/M)^\times$, together with $p \mid M$ (`hpM`), $p^2 \nmid M$ (`hpM2`), the condition `hHp` that every unit of $\mathbb Z/M$ whose image in $\mathbb Z/(M/p)$ is $1$ lies in $H$, and $M/p \neq 0$. Further, a valuation subring $A$ of $\bar{\mathbb Q}$ with $p$ a nonunit of $A$ (`hA`, i.e. $A$ lies over $p$), whose residue field $\kappa = \mathrm{ResidueField}\,A$ has characteristic $p$ and is algebraically closed.
--
--   *Sheets and the diamond.* An automorphism $\theta$ of $F_M$ over $\bar{\mathbb Q}$; two integral $\bar{\mathbb Q}$-algebra maps $\alpha,\beta : F_{M/p} \to F_M$ (`hα`, `hβ`); a unit $pb$ of $\mathbb Z/(M/p)$ whose underlying residue class is $p$ (`hpb`); and a self-map $\delta$ of the set of places of $\bar F$ over $\kappa$ which, by `hδ`, is translation of places by the semilinear automorphism attached to the diamond automorphism $\mathtt{diamondActionModL}$ at $\mathtt{CuspForm.gammaLift}\,(M/p)\,pb$. A finite set $SS$ of pairs of places of $\bar F$ which by `hSS` consists exactly of the pairs belonging to $\mathtt{ssNodePairsQExp}$, that is, pairs $s$ with $s_2$ a supersingular place and $s_1 = \varphi(s_2)$.
--
--   *Specialisation and prolongation.* A datum $\mathrm{Psp} : \mathtt{JHPlaceSpecialization}\,p\,M\,H\,hpM\,A$, consisting of a surjective map $\mathrm{sp}$ from places of $F_{M/p}$ to places of $\bar F$ and a homomorphism on degree-zero Picard groups, subject to the structure's axioms (divisor-to-divisor compatibility with coefficientwise reduction of Laurent series with $A$-coefficients, invariance under inertia, transformation into $\varphi$ under Frobenius elements, and Picard compatibility). Its two readings of a place $W$ of $F_M$ are $\mathrm{red}_1 W = \mathrm{sp}(W|_\alpha)$ and $\mathrm{red}_2 W = \delta(\mathrm{sp}(W|_\beta))$, restriction being along $\alpha$, resp. $\beta$. A place $v$ of $\bar F$ is *fixed* when $\varphi(\delta(\varphi(v))) = v$, and *affine* when some element of $\bar F$ with $q$-expansion $\mathtt{jqModC}$ has a finite value at $v$. A place $W$ of $F_M$ is *strict of the first kind* when $\delta(\varphi(\mathrm{red}_1 W)) = \mathrm{red}_2 W$ and $\mathrm{red}_1 W$ is not fixed, and *strict of the second kind* when $\mathrm{red}_1 W = \varphi(\mathrm{red}_2 W)$ and $\mathrm{red}_2 W$ is not fixed. Also given is $\mathrm{Rpd} : \mathrm{Psp}.\mathtt{ProlongationDatum}\,\theta$: two regular prolongations $R_1, R_2$ of $A$ to $F_M$ with residue maps onto $\bar F$, such that $R_1$'s residue map computes coefficientwise reduction on elements of $F_M$ coming from Laurent series with coefficients in $A$, while $R_2.\mathrm{integers}$ is the $\theta$-preimage of $R_1.\mathrm{integers}$ and $R_2$'s residue of $f$ equals $R_1$'s residue of $\theta f$.
--
--   *The law block.* `hTD` (type dichotomy): every place of $F_M$ satisfies $\mathrm{red}_1 W = \varphi(\mathrm{red}_2 W)$ or $\delta(\varphi(\mathrm{red}_1 W)) = \mathrm{red}_2 W$. `hFix`: the set of fixed places of $\bar F$ is finite. `hmodel`: $\mathrm{Rpd}$ is a model for $(\alpha,\beta,\delta)$, i.e. the four laws hold for every $f \in F_M$ lying in both rings of integers with both residues nonzero and every divisor $D$ with $D\,W = \mathrm{ord}_W f$ — the first divisor law ($\mathrm{red}_1$-pushforward of the restriction of $D$ to places strict of the first kind computes $\mathrm{ord}_v$ of the first residue at every non-fixed $v$), the second divisor law (likewise with $\mathrm{red}_2$, strictness of the second kind and the second residue), and the two cusp laws (the $\mathrm{red}_1$-pushforward of the restriction of $D$ to $\infty$-side places computes $\mathrm{ord}_{\mathrm{red}_1 C}$ of the first residue at every $\infty$-side place $C$, and symmetrically for $0$-side places, $\mathrm{red}_2$ and the second residue). `hO` (order law at fixed affine places): for such $f$ and $D$ and every fixed affine $v$, the $\mathrm{red}_1$-pushforward of $D$ at $v$ equals $\mathrm{ord}_v$ of the first residue plus $\mathrm{ord}_{\delta(\varphi(v))}$ of the second residue. `hRL` (regularity law, two clauses): for $f$ in both rings of integers, if $\mathrm{ord}_V f \ge 0$ at all $V$ with $\mathrm{red}_1 V = v$ for a fixed affine $v$, then $\mathrm{ord}_v$ of the first residue and $\mathrm{ord}_{\delta(\varphi(v))}$ of the second residue are $\ge 0$ whenever the respective residue is nonzero; and for $s \in SS$, if $\mathrm{ord}_V f \ge 0$ at all $V$ with $\mathrm{red}_1 V = s_1$, then the two residues take a common value $c \in \kappa$ at $s_1$ and $s_2$. `hNV` (node-value law): for $f$ with both residues nonzero and $s \in SS$, if no place $V$ with $\mathrm{ord}_V f \neq 0$ has $(\mathrm{red}_1 V, \mathrm{red}_2 V) = s$, then the two residues take a common nonzero value at $s_1$ and $s_2$.
--
--   *The pins.* `hα_coe`: $\alpha$ is the identity on $q$-expansions. `hβ_coe`: $\beta$ acts as $\mathtt{qExpand}\,p$ (substitution $q \mapsto q^p$) on $q$-expansions. `hθgal`: $\theta$ commutes with the semilinear arithmetic Galois action $\mathtt{arithmeticGalois}$ of $\mathrm{Gal}(\bar{\mathbb Q}/\mathbb Q)$ on $F_M$. `hβθ`: $\beta$ equals $\alpha$ followed by $\theta$.
--
--   *The two residual pole bounds.* `hLFst`: for places $Q \neq Q'$ strict of the first kind with $\mathrm{red}_1 Q' = \mathrm{red}_1 Q$ affine, for $n \in \mathbb N$ nonzero in $\kappa$, for $g \in R_1.\mathrm{integers}$ with nonzero first residue, $\mathrm{ord}_Q g = -n$, $\mathrm{ord}_{Q'} g = n$ and $\mathrm{ord}_W g = 0$ for all other places $W$ strict of the first kind with the same first reading as $Q$, and for $e \in A$ and $\varepsilon \in R_1.\mathrm{integers}$ with nonzero first residue such that $g = 1 + e\varepsilon$, one has $\mathrm{ord}_{\mathrm{red}_1 Q}$ of the first residue of $\varepsilon$ at least $-1$. `hLSnd` is the same statement with 'first kind', $\mathrm{red}_1$, $R_1$ replaced by 'second kind', $\mathrm{red}_2$, $R_2$.
--
--   *The modular-unit clause* `hUnit`: there exist $u_1, u_2 \in F_M$ and divisors $D_1, D_2$ with $D_i\,W = \mathrm{ord}_W u_i$ such that: $u_1$ and $u_1^{-1}$ lie in $R_1.\mathrm{integers}$, the first residue of $u_1$ is nonzero, the first divisor law holds for $D_1$ at every non-fixed place and the $\infty$-side cusp law holds for $D_1$; for every nonzero $f \in F_M$ there are $m \neq 0$ in $\mathbb N$ and $j \in \mathbb Z$ with $f^m u_1^{\,j} \in R_2.\mathrm{integers}$ of nonzero second residue; symmetrically, $u_2$ and $u_2^{-1}$ lie in $R_2.\mathrm{integers}$, the second residue of $u_2$ is nonzero, the second divisor law holds for $D_2$ at every non-fixed place and the $0$-side cusp law holds for $D_2$; and for every nonzero $f$ there are $m \neq 0$ and $j$ with $f^m u_2^{\,j} \in R_1.\mathrm{integers}$ of nonzero first residue.
--
--   *The cusp-fibre and orientation clauses.* `hcusp`: every non-affine place $w$ of $\bar F$ is of the form $\mathrm{red}_1 C$ for some $\infty$-side place $C$ and also of the form $\mathrm{red}_2 C'$ for some $0$-side place $C'$. Here $C$ is on the $\infty$-side when $C$ is cuspidal for $j$ (for every $x$ with $q$-expansion $\mathtt{jqModC}$ and every $a \in A$, $\mathrm{ord}_C(x - a) \le 0$) and $x'/x^p$ has a value at $C$ with residue $1$, for some $x, x'$ with $q$-expansions $j(q)$ and $j(q^p)$; and on the $0$-side when $C$ is cuspidal for $j(q^p)$ and $x/x'^p$ has a value at $C$ with residue $1$. `horientInf`: for every $\infty$-side place $C$, $\delta(\varphi(\mathrm{red}_1 C)) = \mathrm{red}_2 C$. `horient0`: for every $0$-side place $C$, $\mathrm{red}_1 C = \varphi(\mathrm{red}_2 C)$.
--
--   *The target data.* A place $V_0$ of $F_M$ which is either on the $0$-side or strict of the second kind (`hV₀`), a finite set $S$ of elements of $\kappa$ and a finite set $B$ of places of $\bar F$.
--
--   *Conclusion.* There exists $g \in F_M$ lying in $R_1.\mathrm{integers}$ and in $R_2.\mathrm{integers}$ such that:
--
--   1. the $R_1$-residue of $g$ is nonzero;
--
--   2. the $R_2$-residue of $g$ is nonzero;
--
--   3. $\mathrm{ord}_{V_0}(g) = -1$;
--
--   4. for every place $V$ of $F_M$ with $V \neq V_0$ and $\mathrm{ord}_V(g) < 0$: for every $x_j \in F_M$ whose $q$-expansion is $\mathtt{jqModC}$ there is $a \in A$ with $\mathrm{ord}_V\bigl(x_j - a\bigr) > 0$ and with the residue of $a$ in $\kappa$ outside $S$; and moreover $\mathrm{red}_1 V \notin B$ and $\mathrm{red}_2 V \notin B$;
--
--   5. $\mathrm{ord}_{\mathrm{red}_2 V_0}$ of the $R_2$-residue of $g$ equals $-1$.
--
--   This is the construction, in the two-sheeted reduction picture for $X_H$ at a prime $p$ exactly dividing the level, of a function that is a unit for both regular prolongations, has a simple pole at a prescribed place $V_0$ on the $0$-side or strict of the second kind, whose second reading has a simple pole at $\mathrm{red}_2 V_0$, and whose remaining poles avoid a prescribed finite set of reductions and have $j$-values with residues outside a prescribed finite set. It feeds the production of principal divisors supported at controlled places, being cited by [`ModularCurve.JHPlaceSpecialization.exists_isPrincipal_apply_eq_neg_one_forall_support_good_of_isZeroSide_or_isStrictSnd`](thm.html#ModularCurve.JHPlaceSpecialization.exists_isPrincipal_apply_eq_neg_one_forall_support_good_of_isZeroSide_or_isStrictSnd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHPlaceSpecialization_ProlongationDatum_exists_commonUnit_pole_reduceSnd_of_regularityLaw_of_coe_of_unit_of_cusp_of_orient.lean

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

theorem ModularCurve.JHPlaceSpecialization.ProlongationDatum.exists_commonUnit_pole_reduceSnd_of_regularityLaw_of_coe_of_unit_of_cusp_of_orient
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

    (V₀ : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (hV₀ : JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A) V₀ ∨ Psp.IsStrictSnd α β hα hβ δ V₀)
    (S : Finset (ResidueField ↥A)) (B : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))) :
    ∃ (g : ↥(xHFunctionFieldBar M H)) (h₁ : g ∈ Rpd.R₁.integers) (h₂ : g ∈ Rpd.R₂.integers),
      Rpd.R₁.residue ⟨g, h₁⟩ ≠ 0 ∧ Rpd.R₂.residue ⟨g, h₂⟩ ≠ 0 ∧ V₀.ord g = -1 ∧
      (∀ V, V ≠ V₀ → V.ord g < 0 →
        (∀ (xj : ↥(xHFunctionFieldBar M H)), ((xj : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ) →
          ∃ a : ↥A, 0 < V.ord (xj - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a : AlgebraicClosure ℚ)) ∧ IsLocalRing.residue ↥A a ∉ S) ∧
          Psp.reduceFst α hα V ∉ B ∧ Psp.reduceSnd β hβ δ V ∉ B) ∧
      (Psp.reduceSnd β hβ δ V₀).ord (Rpd.R₂.residue ⟨g, h₂⟩) = -1 := by sorry
