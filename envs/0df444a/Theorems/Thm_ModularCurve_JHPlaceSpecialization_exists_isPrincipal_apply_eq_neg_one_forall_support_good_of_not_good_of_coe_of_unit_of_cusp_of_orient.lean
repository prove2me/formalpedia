-- Prove2me | Theorems.Thm_ModularCurve_JHPlaceSpecialization_exists_isPrincipal_apply_eq_neg_one_forall_support_good_of_not_good_of_coe_of_unit_of_cusp_of_orient
-- name    : ModularCurve.JHPlaceSpecialization.exists_isPrincipal_apply_eq_neg_one_forall_support_good_of_not_good_of_coe_of_unit_of_cusp_of_orient
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/0279001f-d3d5-56d1-ad5d-e0e140dab9ea
-- title:
--   Removing one bad place by a principal divisor
-- statement:
--   Throughout, write $\kappa$ for the residue field of the valuation subring $A$, $F_M$ for `xHFunctionFieldBar M H` (the $\overline{\mathbb Q}$-base change of the function field `xHFunctionField M H` inside Laurent series), $F_{M/p}$ for `xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)`, where `infSubgroup p M H hpM` is the image of $H$ under $(\mathbb Z/M)^\times \to (\mathbb Z/(M/p))^\times$, and $\bar F$ for `JHNeronObjectAtP.Fbar p M H hpM κ`, the characteristic-$p$ $q$-expansion function field attached to the group `JHNeronObjectAtP.ΓN p M H hpM`. For places, $\mathrm{ord}_V$ denotes the normalised order function of a `Place`, a divisor is a finitely supported function from places to $\mathbb Z$, $\deg$ is the degree homomorphism $D \mapsto \sum_V D(V)\,\deg V$, and a divisor $D$ is principal when there is a nonzero $f$ with $D(V) = \mathrm{ord}_V(f)$ for all $V$. Write $\Phi =$ `qExpFrobeniusPlaceModL κ (JHNeronObjectAtP.ΓN p M H hpM) p` for the operation on places of $\bar F$ given by restriction along the mod-$p$ Frobenius of the $q$-expansion function field.
--
--   *Level and base data.* A prime $p$ and a nonzero modulus $M$ with $p \mid M$ and $p^2 \nmid M$ (`hpM`, `hpM2`), a subgroup $H \le (\mathbb Z/M)^\times$ containing every unit which reduces to $1$ in $(\mathbb Z/(M/p))^\times$ (`hHp`), with $M/p$ nonzero; a valuation subring $A$ of $\overline{\mathbb Q}$ with $p$ a non-unit of $A$ (`hA`, the predicate `LiesOverPrime`), whose residue field $\kappa$ has characteristic $p$ and is algebraically closed.
--
--   *Function-field data.* A $\overline{\mathbb Q}$-algebra automorphism $\theta$ of $F_M$; two $\overline{\mathbb Q}$-algebra maps $\alpha, \beta : F_{M/p} \to F_M$, both integral (`hα`, `hβ`). For a place $W$ of $F_M$ set $\mathrm{red}_1 W = \mathrm{sp}(W|_\alpha)$ and $\mathrm{red}_2 W = \delta(\mathrm{sp}(W|_\beta))$, where $\mathrm{sp}$ is the place map of the specialization datum below and $W|_\alpha$, $W|_\beta$ are the restrictions of $W$ along $\alpha$, $\beta$.
--
--   *Diamond operator.* A unit $pb$ of $\mathbb Z/(M/p)$ whose underlying residue is $p$ (`hpb`), and a self-map $\delta$ of the places of $\bar F$ which (`hδ`) is the action, through `SemilinearAut.ofAlgAut`, of the diamond automorphism `diamondActionModL κ (M/p) (infSubgroup p M H hpM)` evaluated at the $\Gamma_0(M/p)$-lift [`CuspForm.gammaLift (M/p) pb`](def/CuspForm_HeckeOperatorFormsGammaH.html#L36) of $pb$.
--
--   *Supersingular node pairs.* A finite set $SS$ of pairs of places of $\bar F$ which (`hSS`) consists exactly of the pairs $s$ with $s_2$ a supersingular place and $s_1 = \Phi(s_2)$, i.e. of the members of `ssNodePairsQExp κ (JHNeronObjectAtP.ΓN p M H hpM) p`.
--
--   *Specialization and prolongation.* A datum $Psp$ of type `JHPlaceSpecialization p M H hpM A` (a place map $\mathrm{sp}$ from places of $F_{M/p}$ to places of $\bar F$, a homomorphism on degree-zero divisor classes, compatibility of $\mathrm{sp}$ with reduction of $q$-expansion coefficients and with principal divisors, surjectivity of $\mathrm{sp}$, and inertia- and Frobenius-equivariance for the arithmetic Galois action), and a datum $Rpd$ of type `ProlongationDatum Psp θ`, consisting of two regular prolongations $R_1, R_2$ of $A$ to $F_M$ with residue values in $\bar F$, the compatibility of $R_1$ with coefficientwise reduction of Laurent series over $A$, and the identification of $R_2$ with $R_1$ transported by $\theta$.
--
--   *The laws.* `hTD` (type dichotomy): for every place $W$ of $F_M$, either $\mathrm{red}_1 W = \Phi(\mathrm{red}_2 W)$ or $\delta(\Phi(\mathrm{red}_1 W)) = \mathrm{red}_2 W$. `hFix`: the set of places $v$ of $\bar F$ with $\Phi(\delta(\Phi v)) = v$ (the $\delta$-fixed places) is finite. `hmodel`: $Rpd$ is a model for $\alpha,\beta,\delta$, that is, the two divisor laws, the cusp law at the $\infty$-side and the cusp law at the zero-side hold. `hO`: the order law at fixed affine places, computing $\mathrm{red}_1$-pushforwards of principal divisors as a sum of two residue orders. `hRL`: the regularity law relative to $SS$ (positivity of residue orders at fixed affine places, and existence of a common value at each node pair). `hNV`: the node-value law relative to $SS$ (a nonzero common value at a node pair for functions whose divisor misses that pair). A place $W$ of $F_M$ is of *strict first type* when $\delta(\Phi(\mathrm{red}_1 W)) = \mathrm{red}_2 W$ and $\mathrm{red}_1 W$ is not $\delta$-fixed, and of *strict second type* when $\mathrm{red}_1 W = \Phi(\mathrm{red}_2 W)$ and $\mathrm{red}_2 W$ is not $\delta$-fixed; `fstDiv`, `sndDiv` denote the restrictions of a divisor to the places of the respective strict type.
--
--   *The pins.* `hα_coe`: $\alpha$ is the identity on $q$-expansions. `hβ_coe`: $\beta$ acts on $q$-expansions by $q \mapsto q^p$, that is by `qExpand (AlgebraicClosure ℚ) p`. `hθgal`: $\theta$ commutes with the arithmetic Galois action of $\mathrm{Aut}(\overline{\mathbb Q}/\mathbb Q)$ on $F_M$. `hβθ`: $\beta = \theta \circ \alpha$.
--
--   *The two local laws.* `hLFst`: for all places $Q, Q'$ of $F_M$ of strict first type with $\mathrm{red}_1 Q' = \mathrm{red}_1 Q$, $Q' \neq Q$ and $\mathrm{red}_1 Q$ an affine place (a place of $\bar F$ which takes a value in $\kappa$ at an element with Laurent expansion `jqModC κ`), for every natural $n$ whose image in $\kappa$ is nonzero, and every $g \in F_M$ lying in the integers of $R_1$ with nonzero $R_1$-residue, such that $\mathrm{ord}_Q(g) = -n$, $\mathrm{ord}_{Q'}(g) = n$ and $\mathrm{ord}_W(g) = 0$ for every further place $W$ of strict first type with $\mathrm{red}_1 W = \mathrm{red}_1 Q$ and $W \neq Q, Q'$: if $e \in A$ and $\varepsilon$ lies in the integers of $R_1$ with nonzero $R_1$-residue and $g = 1 + e\,\varepsilon$, then $-1 \le \mathrm{ord}_{\mathrm{red}_1 Q}$ of the $R_1$-residue of $\varepsilon$. `hLSnd` is the same statement with the strict second type, $\mathrm{red}_2$ and $R_2$ throughout.
--
--   *The unit clause* `hUnit`: there are $u_1, u_2 \in F_M$ and divisors $D_1, D_2$ with $D_1(W) = \mathrm{ord}_W(u_1)$ and $D_2(W) = \mathrm{ord}_W(u_2)$ for all $W$, such that: $u_1$ and $u_1^{-1}$ lie in the integers of $R_1$ and the $R_1$-residue of $u_1$ is nonzero; the $\mathrm{red}_1$-pushforward of the strict-first part of $D_1$ agrees at every non-$\delta$-fixed place $v$ with $\mathrm{ord}_v$ of that residue; for every $\infty$-side place $C$ the $\mathrm{red}_1$-pushforward of the restriction of $D_1$ to the $\infty$-side places takes at $\mathrm{red}_1 C$ the value $\mathrm{ord}_{\mathrm{red}_1 C}$ of that residue; and for every nonzero $f \in F_M$ there are $m \neq 0$ in $\mathbb N$ and $j \in \mathbb Z$ with $f^m u_1^{\,j}$ in the integers of $R_2$ and with nonzero $R_2$-residue. Symmetrically, $u_2$ and $u_2^{-1}$ lie in the integers of $R_2$ with nonzero $R_2$-residue, the $\mathrm{red}_2$-pushforward of the strict-second part of $D_2$ computes $\mathrm{ord}_v$ of that residue at every non-$\delta$-fixed $v$, the $\mathrm{red}_2$-pushforward of the restriction of $D_2$ to the zero-side places computes $\mathrm{ord}_{\mathrm{red}_2 C}$ of that residue at every zero-side place $C$, and for every nonzero $f$ there are $m \neq 0$ and $j$ with $f^m u_2^{\,j}$ in the integers of $R_1$ with nonzero $R_1$-residue. Here a place $C$ of $F_M$ is on the $\infty$-side when it is cuspidal ($\mathrm{ord}_C(x - a) \le 0$ for every $x$ with expansion `jqModC` and every $a \in A$) and takes at $x'/x^p$ a value $\tau \in A$ with residue $1$, for some $x, x'$ with expansions $j(q)$ and $j(q^p)$; it is on the zero-side when it is cuspidal for $j(q^p)$ in the same sense and takes such a value at $x/x'^{\,p}$.
--
--   *The cusp-fibre clause* `hcusp`: every place $w$ of $\bar F$ which is not an affine place is both $\mathrm{red}_1 C$ for some $\infty$-side place $C$ and $\mathrm{red}_2 C$ for some zero-side place $C$.
--
--   *The orientation clauses.* `horientInf`: $\delta(\Phi(\mathrm{red}_1 C)) = \mathrm{red}_2 C$ for every $\infty$-side place $C$. `horient0`: $\mathrm{red}_1 C = \Phi(\mathrm{red}_2 C)$ for every zero-side place $C$.
--
--   *Good and bad places.* A finite set $S \subseteq \kappa$ all of whose elements lie outside `ssJSet p κ`, the set of those $j \in \kappa$ for which every elliptic curve with $j$-invariant $j$ has trivial $p$-torsion (`hS`); an element $xj \in F_M$ whose Laurent expansion is `jqModC (AlgebraicClosure ℚ)` (`hxj`); and a place $V_0$ of $F_M$. Call a place $V$ *good* if there is $a \in A$ with $0 < \mathrm{ord}_V(xj - a)$ and with residue of $a$ in $\kappa$ not lying in $S$. The hypothesis `hbad` states that $V_0$ is not good.
--
--   *Conclusion.* There exists a divisor $p'$ on $F_M$ over $\overline{\mathbb Q}$ such that: $p'$ is principal, that is $p'(V) = \mathrm{ord}_V(f)$ for all places $V$ and some nonzero $f \in F_M$; $p'(V_0) = -1$; $\deg p' = 0$; and every $V$ in the support of $p'$ with $V \neq V_0$ is good, i.e. there is $a \in A$ with $0 < \mathrm{ord}_V(xj - a)$ and the residue of $a$ outside $S$.
--
--   This is the place-avoidance step in the study of specialisation of places of the function field of $X_H(M)$ at the prime $p$: a single bad place may be cancelled by a principal degree-zero divisor whose remaining support consists only of good places, i.e. of places at which the $j$-invariant has a non-supersingular reduction outside the prescribed finite set $S$. It is invoked in the construction of a representative of a divisor class all of whose support is good, and the case analysis on $V_0$ (cuspidal, fixed affine, strict first or second type, $\infty$- or zero-side) is supplied by the companion dichotomy results.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHPlaceSpecialization_exists_isPrincipal_apply_eq_neg_one_forall_support_good_of_not_good_of_coe_of_unit_of_cusp_of_orient.lean

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

theorem ModularCurve.JHPlaceSpecialization.exists_isPrincipal_apply_eq_neg_one_forall_support_good_of_not_good_of_coe_of_unit_of_cusp_of_orient
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

    (S : Finset (ResidueField ↥A)) (hS : ∀ s ∈ S, s ∉ @ssJSet p (ResidueField ↥A) _ (Classical.decEq _))
    (xj : ↥(xHFunctionFieldBar M H)) (hxj : ((xj : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ))

    (V₀ : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (hbad : ¬ ∃ a : ↥A, 0 < V₀.ord (xj - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a : AlgebraicClosure ℚ)) ∧ IsLocalRing.residue ↥A a ∉ S) :
    ∃ p' : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
      Divisor.IsPrincipal p' ∧ p' V₀ = -1 ∧ Divisor.degree p' = 0 ∧
        ∀ V ∈ p'.support, V ≠ V₀ →
          ∃ a : ↥A, 0 < V.ord (xj - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a : AlgebraicClosure ℚ)) ∧ IsLocalRing.residue ↥A a ∉ S := by sorry
