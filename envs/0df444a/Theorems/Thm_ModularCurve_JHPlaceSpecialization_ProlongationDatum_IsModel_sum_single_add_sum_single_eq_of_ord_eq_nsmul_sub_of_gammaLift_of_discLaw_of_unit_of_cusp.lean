-- Prove2me | Theorems.Thm_ModularCurve_JHPlaceSpecialization_ProlongationDatum_IsModel_sum_single_add_sum_single_eq_of_ord_eq_nsmul_sub_of_gammaLift_of_discLaw_of_unit_of_cusp
-- name    : ModularCurve.JHPlaceSpecialization.ProlongationDatum.IsModel.sum_single_add_sum_single_eq_of_ord_eq_nsmul_sub_of_gammaLift_of_discLaw_of_unit_of_cusp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/04df1d68-373f-50fd-ba00-d878e7177319
-- title:
--   Rigidity of divisors with equal first-kind and second-kind reductions
-- statement:
--   Fix a prime $p$ and a positive integer $M$ with $p \mid M$ and $p^2 \nmid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$ such that every unit of $\mathbb{Z}/M$ whose image under reduction to $(\mathbb{Z}/(M/p))^\times$ is trivial lies in $H$, and a valuation subring $A$ of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $A$ (`LiesOverPrime`), whose residue field $\kappa$ has characteristic $p$ and is algebraically closed. Write $F_M =$ `xHFunctionFieldBar M H` for the base change to $\overline{\mathbb{Q}}$ of the function field of $X_H(M)$ inside Laurent series, $F_{M/p} =$ `xHFunctionFieldBar (M/p) (infSubgroup p M H hpM)` for the corresponding field at level $M/p$ with the image subgroup, and $\bar F =$ `JHNeronObjectAtP.Fbar p M H hpM κ` for the characteristic-$p$ $q$-expansion function field. Divisors are finitely supported $\mathbb{Z}$-valued functions on places, and `Place.ord` is the normalised additive valuation.
--
--   The data are: an $\overline{\mathbb{Q}}$-algebra automorphism $\theta$ of $F_M$; two integral $\overline{\mathbb{Q}}$-algebra maps $\alpha, \beta : F_{M/p} \to F_M$ (hypotheses $h\alpha$, $h\beta$); a unit $pb$ of $\mathbb{Z}/(M/p)$ whose underlying residue is $p$; a self-map $\delta$ of the set of places of $\bar F$ over $\kappa$ which, by $h\delta$, is the action of the semilinear automorphism attached by `diamondActionModL` to the $\Gamma_0(M/p)$-lift [`CuspForm.gammaLift (M/p) pb`](def/CuspForm_HeckeOperatorFormsGammaH.html#L36) of $pb$; a finite set $SS$ of pairs of places of $\bar F$ which, by $hSS$, is exactly `ssNodePairsQExp κ (ΓN p M H hpM) p`, i.e. the set of pairs $s$ with $s_2$ supersingular and $s_1$ the Frobenius place of $s_2$; a specialisation datum $Psp :$ `JHPlaceSpecialization p M H hpM A` and a prolongation datum $Rpd$ for $Psp$ and $\theta$, consisting of two regular prolongations $R_1, R_2$ of $A$ from $F_M$ to $\bar F$ linked by $\theta$. Throughout, `reduceFst` $Q = Psp.sp(Q|_\alpha)$ and `reduceSnd` $Q = \delta(Psp.sp(Q|_\beta))$ denote the two reductions of a place $Q$ of $F_M$, a place $W$ is strict of the first kind when $\delta(\mathrm{Frob}(\mathrm{reduceFst}\,W)) = \mathrm{reduceSnd}\,W$ and $\mathrm{reduceFst}\,W$ is not $\delta$-fixed, strict of the second kind when $\mathrm{reduceFst}\,W = \mathrm{Frob}(\mathrm{reduceSnd}\,W)$ and $\mathrm{reduceSnd}\,W$ is not $\delta$-fixed, and a place $v$ of $\bar F$ is affine when the $j$-function has a value in $\kappa$ at $v$.
--
--   The structural hypotheses are: the type dichotomy $hTD$ (every place of $F_M$ satisfies at least one of the two displayed compatibilities between its two reductions); the model hypothesis $hmodel$, the conjunction of the two divisor laws (for $f$ integral with non-zero residue for both $R_1$ and $R_2$, the push-forward along `reduceFst` of the first-kind part of $\operatorname{div} f$ computes the order of the $R_1$-residue of $f$ at every non-$\delta$-fixed place, and symmetrically for the second-kind part, `reduceSnd` and $R_2$) and the two cusp laws (the same identities for the infinity-side part along `reduceFst` and the zero-side part along `reduceSnd`); the order law at fixed places $hO$ (at a $\delta$-fixed affine place $v$ the push-forward of the whole divisor equals the sum of the orders of the two residues at $v$ and at $\delta(\mathrm{Frob}\,v)$); the regularity law $hRL$ (two clauses: non-negativity of the residue orders at $\delta$-fixed affine places, and existence of a common value of the two residues at each node pair in $SS$, both under the assumption that $\operatorname{ord} f \ge 0$ above the place concerned); and the node value law $hNV$ (at each $s \in SS$ avoided by the divisor of $f$, the two residues take a common non-zero value at $s_1$ and $s_2$).
--
--   The compatibility hypotheses are: $h\alpha_{\mathrm{coe}}$, that $\alpha$ is the identity on $q$-expansions; $h\beta_{\mathrm{coe}}$, that $\beta$ is the substitution $q \mapsto q^p$ (`qExpand`); $h\theta\mathrm{gal}$, that $\theta$ commutes with the arithmetic Galois action of $\overline{\mathbb{Q}} \simeq_{\mathbb{Q}} \overline{\mathbb{Q}}$ on $F_M$; and $h\beta\theta$, that $\beta$ is $\alpha$ followed by $\theta$.
--
--   The two disc laws $hLFst$ and $hLSnd$ are local simple-pole statements. $hLFst$ requires: for all places $Q, Q'$ of $F_M$ strict of the first kind with $\mathrm{reduceFst}\,Q' = \mathrm{reduceFst}\,Q$, $Q' \ne Q$ and $\mathrm{reduceFst}\,Q$ affine, for every $n \in \mathbb{N}$ with $n \ne 0$ in $\kappa$, every $g$ in the integers of $R_1$ with non-zero $R_1$-residue such that $Q.\mathrm{ord}\,g = -n$, $Q'.\mathrm{ord}\,g = n$ and $W.\mathrm{ord}\,g = 0$ for every other strict first-kind place $W$ with the same `reduceFst`, and every $e \in A$ and $\varepsilon$ in the integers of $R_1$ with non-zero residue such that $g = 1 + e\varepsilon$, the order of the $R_1$-residue of $\varepsilon$ at $\mathrm{reduceFst}\,Q$ is at least $-1$. The hypothesis $hLSnd$ is the same statement with the second kind, `reduceSnd` and $R_2$.
--
--   The modular-unit hypothesis $hUnit$ asserts the existence of $u_1, u_2 \in F_M$ and divisors $D_1, D_2$ with $D_1 W = W.\mathrm{ord}\,u_1$ and $D_2 W = W.\mathrm{ord}\,u_2$ for all $W$, such that: $u_1$ and $u_1^{-1}$ lie in the integers of $R_1$, the $R_1$-residue of $u_1$ is non-zero, the push-forward along `reduceFst` of the first-kind part of $D_1$ agrees with the order of that residue at every non-$\delta$-fixed place, and the push-forward along `reduceFst` of the infinity-side part of $D_1$ agrees with the order of that residue at $\mathrm{reduceFst}\,C$ for every infinity-side place $C$; every non-zero $f \in F_M$ admits $m \ne 0$ in $\mathbb{N}$ and $j \in \mathbb{Z}$ with $f^m u_1^{j}$ in the integers of $R_2$ and of non-zero $R_2$-residue; and the mirror-image clauses for $u_2$, $R_2$, the second-kind part, `reduceSnd`, the zero-side places, and $f^m u_2^{j}$ in the integers of $R_1$ with non-zero $R_1$-residue.
--
--   The cusp-cover hypothesis $hcusp$ asserts that every non-affine place $w$ of $\bar F$ is simultaneously the `reduceFst`-image of some infinity-side place of $F_M$ and the `reduceSnd`-image of some zero-side place.
--
--   Finally, the configuration: natural numbers $d_1, d_2$; families $Q_1 : \mathrm{Fin}\,d_1 \to$ places of $F_M$ and $Q_2 : \mathrm{Fin}\,d_2 \to$ places, strict of the first and second kind respectively, with $i \mapsto \mathrm{reduceFst}(Q_1 i)$ and $j \mapsto \mathrm{reduceSnd}(Q_2 j)$ injective; families $Q_1', Q_2'$ of the same lengths, again strict of the first and second kind, with $\mathrm{reduceFst}(Q_1' i) = \mathrm{reduceFst}(Q_1 i)$ for all $i$ and $\mathrm{reduceSnd}(Q_2' j) = \mathrm{reduceSnd}(Q_2 j)$ for all $j$; finite sets $T_1, T_2$ of places of $\bar F$ characterised by $v \in T_1 \iff v = \mathrm{reduceFst}(Q_1 i)$ for some $i$ and $v \in T_2 \iff v = \mathrm{reduceSnd}(Q_2 j)$ for some $j$, with $T_1$ disjoint from the set of first coordinates of $SS$ and all members of $T_1$ and of $T_2$ affine; the general-position hypotheses $hgp_1$ (any $h \in \bar F$ with non-negative order outside $T_1$, order at least $-1$ on $T_1$ and value $0$ at each first coordinate of a pair in $SS$ is zero) and $hgp_2$ (any $h \in \bar F$ with non-negative order outside $T_2$ and order at least $-1$ on $T_2$ lies in the image of $\kappa$); one further place $Q_s$, strict of the first kind, with $\mathrm{reduceFst}\,Q_s \ne \mathrm{reduceFst}(Q_1 i)$ for all $i$; a natural number $n$ with $n \ne 0$ in $\kappa$; and a non-zero $f \in F_M$ whose divisor satisfies, at every place $V$ of $F_M$,
--   $$V.\mathrm{ord}\,f = n \cdot \Bigl(\sum_i \mathrm{single}(Q_1' i) + \sum_j \mathrm{single}(Q_2' j) - \sum_i \mathrm{single}(Q_1 i) - \sum_j \mathrm{single}(Q_2 j)\Bigr)(V).$$
--
--   The conclusion is the equality of divisors
--   $$\sum_i \mathrm{single}(Q_1' i)(1) + \sum_j \mathrm{single}(Q_2' j)(1) = \sum_i \mathrm{single}(Q_1 i)(1) + \sum_j \mathrm{single}(Q_2 j)(1),$$
--   all coefficients being $1$; that is, the two effective divisors formed from the primed and unprimed families coincide.
--
--   This is the rigidity step in the study of the specialisation of $J_H(M)$ at a prime $p$ with $p \parallel M$: a divisor whose $n$-fold difference is principal, and whose first- and second-kind places reduce pairwise to the same places of the characteristic-$p$ fibre, cannot move. It is used by [`ModularCurve.JHPlaceSpecialization.exists_principal_degZero_forall_support_sub_inertia_smul_eq_of_splitting`](thm.html#ModularCurve.JHPlaceSpecialization.exists_principal_degZero_forall_support_sub_inertia_smul_eq_of_splitting) in the analysis of the component structure and Galois action on the reduction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHPlaceSpecialization_ProlongationDatum_IsModel_sum_single_add_sum_single_eq_of_ord_eq_nsmul_sub_of_gammaLift_of_discLaw_of_unit_of_cusp.lean

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

theorem ModularCurve.JHPlaceSpecialization.ProlongationDatum.IsModel.sum_single_add_sum_single_eq_of_ord_eq_nsmul_sub_of_gammaLift_of_discLaw_of_unit_of_cusp
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
    (Q₁' : Fin d₁ → Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (Q₂' : Fin d₂ → Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (hQ₁' : ∀ i, Psp.IsStrictFst α β hα hβ δ (Q₁' i)) (hQ₂' : ∀ j, Psp.IsStrictSnd α β hα hβ δ (Q₂' j))
    (hred₁ : ∀ i, Psp.reduceFst α hα (Q₁' i) = Psp.reduceFst α hα (Q₁ i))
    (hred₂ : ∀ j, Psp.reduceSnd β hβ δ (Q₂' j) = Psp.reduceSnd β hβ δ (Q₂ j))
    {T₁ T₂ : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))}
    (hT₁ : ∀ v, v ∈ T₁ ↔ ∃ i, Psp.reduceFst α hα (Q₁ i) = v) (hT₂ : ∀ v, v ∈ T₂ ↔ ∃ j, Psp.reduceSnd β hβ δ (Q₂ j) = v)
    (hT₁W : Disjoint T₁ (SS.image Prod.fst))
    (hT₁aff : ∀ v ∈ T₁, JHPlaceSpecialization.IsAffinePlace p M H hpM A v) (hT₂aff : ∀ v ∈ T₂, JHPlaceSpecialization.IsAffinePlace p M H hpM A v)
    (hgp₁ : ∀ h : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), (∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), v ∉ T₁ → 0 ≤ v.ord h) → (∀ v ∈ T₁, -1 ≤ v.ord h) → (∀ w ∈ (SS.image Prod.fst), w.HasValue h 0) → h = 0)
    (hgp₂ : ∀ h : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), (∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), v ∉ T₂ → 0 ≤ v.ord h) → (∀ v ∈ T₂, -1 ≤ v.ord h) → ∃ c : (ResidueField ↥A), h = algebraMap (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) c)
    (Qs : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (hQs : Psp.IsStrictFst α β hα hβ δ Qs) (hQs' : ∀ i, Psp.reduceFst α hα Qs ≠ Psp.reduceFst α hα (Q₁ i))
    (n : ℕ) (hn : (n : (ResidueField ↥A)) ≠ 0) (f : ↥(xHFunctionFieldBar M H)) (hf : f ≠ 0)
    (hdiv : ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), V.ord f = (n : ℤ) * (((∑ i, Finsupp.single (Q₁' i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂' j) (1 : ℤ))
          - (∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ)) : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) V)) :
    (∑ i, Finsupp.single (Q₁' i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂' j) (1 : ℤ) : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
      ∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ) := by sorry
