-- Prove2me | Theorems.Thm_ModularCurve_JHPlaceSpecialization_ProlongationDatum_sectionPair_bounds_of_regularityLaw_of_isModel_of_unit_of_cusp
-- name    : ModularCurve.JHPlaceSpecialization.ProlongationDatum.sectionPair_bounds_of_regularityLaw_of_isModel_of_unit_of_cusp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/8c488b81-bd35-5b4a-9fcc-8ea0d34e71d0
-- title:
--   Section-pair bounds on the two components at a node configuration
-- statement:
--   Fix a prime $p$ and a modulus $M$ with $p \mid M$ but $p^2 \nmid M$, and a subgroup $H \le (\mathbb{Z}/M)^{\times}$ containing every unit that maps to $1$ under `ZMod.unitsMap` for the divisibility $(M/p) \mid M$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ lying over $p$ in the sense of `LiesOverPrime` (i.e. $p$ lies in the non-units of $A$), with residue field $\kappa =$ `ResidueField A` of characteristic $p$ and algebraically closed. Write $F_M$ for `xHFunctionFieldBar M H`, the base change to $\overline{\mathbb{Q}}$ of the function field `xHFunctionField M H` inside $\overline{\mathbb{Q}}$-Laurent series, $F_{M/p}$ for `xHFunctionFieldBar (M/p) (infSubgroup p M H hpM)`, where `infSubgroup p M H hpM` is the image of $H$ in $(\mathbb{Z}/(M/p))^{\times}$, and $\bar F$ for `JHNeronObjectAtP.Fbar p M H hpM κ`, the field `qExpFunctionFieldC κ (JHNeronObjectAtP.ΓN p M H hpM)`. Places are in the sense of [`AlgebraicCurve.Place`](def/AlgebraicCurve_DivisorClassGroup.html#L22) (a valuation subring containing the base field, not all of the field, with principal ideals), and $\mathrm{ord}_v$ is the associated $\mathbb{Z}$-valued order function.
--
--   The data are: a $\overline{\mathbb{Q}}$-algebra automorphism $\theta$ of $F_M$; two integral $\overline{\mathbb{Q}}$-algebra maps $\alpha, \beta : F_{M/p} \to F_M$, normalised on $q$-expansions by `hα_coe` (the expansion of $\alpha u$ is that of $u$) and `hβ_coe` (the expansion of $\beta u$ is obtained from that of $u$ by `qExpand κ p`, i.e. $q \mapsto q^{p}$), with $\beta = \theta \circ \alpha$ and with $\theta$ commuting with the arithmetic Galois action `arithmeticGalois` of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ on $F_M$ (`hθgal`); a unit $pb$ of $\mathbb{Z}/(M/p)$ whose underlying residue is $p$; a self-map $\delta$ of the places of $\bar F$ over $\kappa$ which, by `hδ`, is the action on places of the semilinear automorphism attached by `SemilinearAut.ofAlgAut` to the diamond operator `diamondActionModL κ (M/p) (infSubgroup p M H hpM)` evaluated at the chosen lift [`CuspForm.gammaLift (M/p) pb`](def/CuspForm_HeckeOperatorFormsGammaH.html#L36) of $pb$ to $\Gamma_0(M/p)$; and a finite set $SS$ of pairs of places of $\bar F$ which, by `hSS`, is exactly `ssNodePairsQExp κ (JHNeronObjectAtP.ΓN p M H hpM) p`, the set of pairs $s$ with $s.2$ a supersingular place and $s.1$ its Frobenius translate.
--
--   Further, $Psp$ is a `JHPlaceSpecialization p M H hpM A`, providing a specialisation map $\mathrm{sp}$ from places of $F_{M/p}$ to places of $\bar F$ together with its $q$-expansion, surjectivity, divisor, inertia and Frobenius compatibilities and its compatibility with a map on $\mathrm{Pic}^0$; the two readings of a place $W$ of $F_M$ are $r_1(W) = \mathrm{sp}(W|_{\alpha})$ (`reduceFst`) and $r_2(W) = \delta(\mathrm{sp}(W|_{\beta}))$ (`reduceSnd`), where $W|_{\varphi}$ is the restriction along $\varphi$. A place $v$ of $\bar F$ is `Fixed` for $\delta$ when $\mathrm{Frob}(\delta(\mathrm{Frob}(v))) = v$ for the Frobenius operation `qExpFrobeniusPlaceModL`; $W$ is `IsStrictFst` when $\delta(\mathrm{Frob}(r_1(W))) = r_2(W)$ and $r_1(W)$ is not Fixed, and `IsStrictSnd` when $r_1(W) = \mathrm{Frob}(r_2(W))$ and $r_2(W)$ is not Fixed. $Rpd$ is a `ProlongationDatum Psp θ`: a pair of regular prolongations $R_1, R_2$ of $A$ to $F_M$ with residue maps to $\bar F$, the first compatible with reduction of $q$-expansions coefficientwise, and the second obtained from the first through $\theta$ (membership in $R_2$ means $\theta f \in R_1$, and the $R_2$-residue of $f$ is the $R_1$-residue of $\theta f$). The structural laws assumed are: `hTD`, the type dichotomy, that every place $W$ of $F_M$ satisfies $r_1(W) = \mathrm{Frob}(r_2(W))$ or $\delta(\mathrm{Frob}(r_1(W))) = r_2(W)$; `hmodel`, that $Rpd$ is a model, i.e. the conjunction of the two divisor laws (for $f$ with non-zero residues on both sides and $D = \mathrm{div} f$, the $r_1$-push-forward of the strict-first part of $D$ computes $\mathrm{ord}$ of the $R_1$-residue of $f$ at every non-Fixed place, and symmetrically for $r_2$ and the strict-second part) and the two cusp laws (the same equalities for the push-forwards of the infinity-side, resp. zero-side, parts of $D$ at readings of infinity-side, resp. zero-side, places); `hO`, the order law at Fixed affine places, expressing the $r_1$-push-forward of $\mathrm{div} f$ at such a place as the sum of the orders of the two residues; `hRL`, the regularity law relative to $SS$ (two clauses: positivity of residue orders at Fixed affine places, and existence of a common value at the two coordinates of each node pair, under the corresponding positivity hypotheses on $\mathrm{ord} f$); and `hNV`, the node value law relative to $SS$ (a common non-zero value at each node pair not met by the divisor of $f$).
--
--   Two further hypotheses, `hLFst` and `hLSnd`, are local simple-pole laws on the first and second side respectively. In the first, for places $Q \ne Q'$ both strict-first with the same reading $r_1(Q') = r_1(Q)$, that reading being an affine place (`IsAffinePlace`: some element with $q$-expansion $j$ takes a value there), for a natural number $n$ non-zero in $\kappa$, for $g \in R_1$ with non-zero residue such that $\mathrm{ord}_Q g = -n$, $\mathrm{ord}_{Q'} g = n$ and $\mathrm{ord}_W g = 0$ for every other strict-first $W$ with that reading, and for $e \in A$ and $\varepsilon \in R_1$ with non-zero residue such that $g = 1 + e\,\varepsilon$, one has $-1 \le \mathrm{ord}_{r_1(Q)}$ of the $R_1$-residue of $\varepsilon$. The hypothesis `hLSnd` is the same statement with $R_1$, $r_1$ and `IsStrictFst` replaced by $R_2$, $r_2$ and `IsStrictSnd`.
--
--   The modular-unit hypothesis `hUnit` asserts the existence of $u_1, u_2 \in F_M$ and divisors $D_1 = \mathrm{div}\,u_1$, $D_2 = \mathrm{div}\,u_2$ such that: $u_1$ and $u_1^{-1}$ lie in $R_1$ with non-zero $R_1$-residue, the $r_1$-push-forward of the strict-first part of $D_1$ computes the order of that residue at every non-Fixed place of $\bar F$, and the $r_1$-push-forward of the infinity-side part of $D_1$ computes it at the reading of every infinity-side place; every non-zero $f \in F_M$ admits $m \ne 0$ and $j \in \mathbb{Z}$ with $f^{m}u_1^{j} \in R_2$ of non-zero $R_2$-residue; and symmetrically $u_2, u_2^{-1} \in R_2$ with non-zero $R_2$-residue, the $r_2$-push-forward of the strict-second part of $D_2$ computing the order of that residue at every non-Fixed place and the $r_2$-push-forward of the zero-side part of $D_2$ computing it at the reading of every zero-side place, with every non-zero $f$ admitting $m \ne 0$, $j$ with $f^{m}u_2^{j} \in R_1$ of non-zero $R_1$-residue. Here a place $W$ of $F_M$ is cuspidal when $\mathrm{ord}_W(x - a) \le 0$ for every $x$ with $q$-expansion $j(q)$ and every $a \in A$; it is infinity-side when it is cuspidal and there are $x$, $x'$ with expansions $j(q)$, $j(q^{p})$ and $\tau \in A$ of residue $1$ with $W$ taking the value $\tau$ at $x'/x^{p}$, and zero-side when the analogous condition holds with $j(q^{p})$ in the cuspidality clause and the value taken at $x/x'^{p}$. The cusp-covering hypothesis `hcusp` asserts that every non-affine place $w$ of $\bar F$ is of the form $r_1(C)$ for some infinity-side $C$ and also of the form $r_2(C)$ for some zero-side $C$.
--
--   The configuration data are: natural numbers $d_1, d_2$, families $Q_1 : \mathrm{Fin}\,d_1 \to$ places of $F_M$ with all $Q_1(i)$ strict-first and $Q_2 : \mathrm{Fin}\,d_2 \to$ places of $F_M$ with all $Q_2(j)$ strict-second, such that $i \mapsto r_1(Q_1(i))$ and $j \mapsto r_2(Q_2(j))$ are injective; finite sets $T_1, T_2$ of places of $\bar F$ consisting exactly of the values $r_1(Q_1(i))$, respectively $r_2(Q_2(j))$; $T_1$ disjoint from the set of first coordinates of the pairs in $SS$; and all members of $T_1$ and of $T_2$ affine places. Finally, $E$ and $D$ are divisors on $F_M$ with $0 \le E$ and $D$ good (every place in the support of $D$ is strict-first or strict-second), $G$ lies in both $R_1$ and $R_2$ and satisfies
--   $$\mathrm{div}\,G = E - \Big(\sum_i Q_1(i) + \sum_j Q_2(j)\Big) - D,$$
--   and $h_{b,1}, h_{b,2}$ are non-zero elements of $\bar F$ whose divisors are the $r_1$-push-forward of the strict-first part of $D$ and the $r_2$-push-forward of the strict-second part of $D$ respectively; by `hvals`, for each pair $s \in SS$ there is $c \ne 0$ in $\kappa$ such that $h_{b,1}$ has value $c$ at $s.1$ and $h_{b,2}$ has value $c$ at $s.2$.
--
--   The conclusion is the conjunction of five statements about the two sections $\mathrm{res}_1(G)\,h_{b,1}$ and $\mathrm{res}_2(G)\,h_{b,2}$ of $\bar F$, where $\mathrm{res}_i(G)$ denotes the $R_i$-residue of $G$: first, $0 \le \mathrm{ord}_v(\mathrm{res}_1(G)\,h_{b,1})$ for every place $v$ of $\bar F$ with $v \notin T_1$; second, $-1 \le \mathrm{ord}_v(\mathrm{res}_1(G)\,h_{b,1})$ for every $v \in T_1$; third, $0 \le \mathrm{ord}_v(\mathrm{res}_2(G)\,h_{b,2})$ for every place $v \notin T_2$; fourth, $-1 \le \mathrm{ord}_v(\mathrm{res}_2(G)\,h_{b,2})$ for every $v \in T_2$; and fifth, for every pair $s \in SS$ there is $c \in \kappa$ such that $s.1$ takes the value $c$ at $\mathrm{res}_1(G)\,h_{b,1}$ and $s.2$ takes the value $c$ at $\mathrm{res}_2(G)\,h_{b,2}$. In the fifth conjunct $c$ is not required to be non-zero, in contrast with the hypothesis `hvals`.
--
--   This is the regularity and matching step for the pair of sections cut out on the two components of the reduced fibre at $p$ of the modular curve of level $\Gamma_H(M)$ with $p \parallel M$: the two residues of $G$, corrected by $h_{b,1}$ and $h_{b,2}$, are regular away from the prescribed affine readings $T_1$, $T_2$, have at worst simple poles there, and agree at the two coordinates of every supersingular node pair. It is used by [`ModularCurve.JHPlaceSpecialization.ProlongationDatum.IsModel.exists_isStrictFst_isStrictSnd_reduceFst_eq_reduceSnd_eq_pic0Mk_eq_of_isGoodDiv_of_gammaLift_of_unit_of_cusp`](thm.html#ModularCurve.JHPlaceSpecialization.ProlongationDatum.IsModel.exists_isStrictFst_isStrictSnd_reduceFst_eq_reduceSnd_eq_pic0Mk_eq_of_isGoodDiv_of_gammaLift_of_unit_of_cusp), in the analysis of the $p$-component of the Jacobian that underlies level lowering at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHPlaceSpecialization_ProlongationDatum_sectionPair_bounds_of_regularityLaw_of_isModel_of_unit_of_cusp.lean

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

theorem ModularCurve.JHPlaceSpecialization.ProlongationDatum.sectionPair_bounds_of_regularityLaw_of_isModel_of_unit_of_cusp
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

    {d₁ d₂ : ℕ} (Q₁ : Fin d₁ → Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (Q₂ : Fin d₂ → Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (hQ₁ : ∀ i, Psp.IsStrictFst α β hα hβ δ (Q₁ i)) (hQ₂ : ∀ j, Psp.IsStrictSnd α β hα hβ δ (Q₂ j))
    (hinj₁ : Function.Injective fun i => Psp.reduceFst α hα (Q₁ i))
    (hinj₂ : Function.Injective fun j => Psp.reduceSnd β hβ δ (Q₂ j))
    {T₁ T₂ : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))}
    (hT₁ : ∀ v, v ∈ T₁ ↔ ∃ i, Psp.reduceFst α hα (Q₁ i) = v) (hT₂ : ∀ v, v ∈ T₂ ↔ ∃ j, Psp.reduceSnd β hβ δ (Q₂ j) = v)
    (hT₁W : Disjoint T₁ (SS.image Prod.fst))
    (hT₁aff : ∀ v ∈ T₁, JHPlaceSpecialization.IsAffinePlace p M H hpM A v) (hT₂aff : ∀ v ∈ T₂, JHPlaceSpecialization.IsAffinePlace p M H hpM A v)
    (E D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (hE : 0 ≤ E) (hD : Psp.IsGoodDiv α β hα hβ δ D)
    (G : ↥(xHFunctionFieldBar M H)) (h₁ : G ∈ Rpd.R₁.integers) (h₂ : G ∈ Rpd.R₂.integers)
    (hdiv : ∀ V, (E - (∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ)) - D) V = V.ord G)
    (hb₁ hb₂ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) (hb₁0 : hb₁ ≠ 0) (hb₂0 : hb₂ ≠ 0)
    (hdiv₁ : ∀ v, Finsupp.mapDomain (Psp.reduceFst α hα) (Psp.fstDiv α β hα hβ δ D) v = v.ord hb₁)
    (hdiv₂ : ∀ v, Finsupp.mapDomain (Psp.reduceSnd β hβ δ) (Psp.sndDiv α β hα hβ δ D) v = v.ord hb₂)
    (hvals : ∀ s ∈ SS, ∃ c : (ResidueField ↥A), c ≠ 0 ∧ s.1.HasValue hb₁ c ∧ s.2.HasValue hb₂ c) :
    (∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), v ∉ T₁ → 0 ≤ v.ord ((Rpd.R₁.residue ⟨G, h₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) * hb₁)) ∧
    (∀ v ∈ T₁, -1 ≤ v.ord ((Rpd.R₁.residue ⟨G, h₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) * hb₁)) ∧
    (∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), v ∉ T₂ → 0 ≤ v.ord ((Rpd.R₂.residue ⟨G, h₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) * hb₂)) ∧
    (∀ v ∈ T₂, -1 ≤ v.ord ((Rpd.R₂.residue ⟨G, h₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) * hb₂)) ∧
    (∀ s ∈ SS, ∃ c : (ResidueField ↥A), s.1.HasValue ((Rpd.R₁.residue ⟨G, h₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) * hb₁) c ∧ s.2.HasValue ((Rpd.R₂.residue ⟨G, h₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) * hb₂) c) := by sorry
