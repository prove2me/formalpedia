-- Prove2me | Theorems.Thm_ModularCurve_JHPlaceSpecialization_ProlongationDatum_IsModel_exists_hasValue_and_hasValue_residue_reduceFst_of_isStrictFst_of_forall_ord_nonneg_of_unit_of_cusp
-- name    : ModularCurve.JHPlaceSpecialization.ProlongationDatum.IsModel.exists_hasValue_and_hasValue_residue_reduceFst_of_isStrictFst_of_forall_ord_nonneg_of_unit_of_cusp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/8676de4c-fb67-5ead-a93f-77910ce9d4e8
-- title:
--   A-integral value at a strict place of the first kind
-- statement:
--   Fix a prime $p$ and a natural number $M$ with $p \mid M$ but $p^2 \nmid M$, a subgroup $H \le (\mathbb Z/M)^\times$ containing the kernel of reduction $(\mathbb Z/M)^\times \to (\mathbb Z/(M/p))^\times$ (hypothesis `hHp`: every unit $u$ with `ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1` lies in $H$), and a valuation subring $A$ of $\overline{\mathbb Q}$ lying over $p$ in the sense of [`ValuationSubring.LiesOverPrime`](def/FLTPrelim_Ramification.html#L16), i.e. $p$ belongs to the non-units of $A$, whose residue field $\kappa =$ `ResidueField ↥A` has characteristic $p$ and is algebraically closed. Write $F_M =$ `xHFunctionFieldBar M H` for the compositum of $\overline{\mathbb Q}$ with the function field of $X_H(M)$ inside $\overline{\mathbb Q}$-Laurent series, $F_{M/p} =$ `xHFunctionFieldBar (M/p) (infSubgroup p M H hpM)` for the analogous field at level $M/p$ and image subgroup, and $\overline F =$ `JHNeronObjectAtP.Fbar p M H hpM κ`, the $q$-expansion function field over $\kappa$ for the group `JHNeronObjectAtP.ΓN p M H hpM`.
--
--   The geometric data consist of: a $\overline{\mathbb Q}$-algebra automorphism $\theta$ of $F_M$; two $\overline{\mathbb Q}$-algebra maps $\alpha, \beta : F_{M/p} \to F_M$, each integral ($h\alpha$, $h\beta$); a unit $pb$ of $\mathbb Z/(M/p)$ whose underlying residue is $p$ ($hpb$); a self-map $\delta$ of the set of places of $\overline F$ over $\kappa$ which, by $h\delta$, acts as the semilinear automorphism `SemilinearAut.ofAlgAut` attached to the diamond operator `diamondActionModL κ (M/p) (infSubgroup p M H hpM)` evaluated at [`CuspForm.gammaLift (M/p) pb`](def/CuspForm_HeckeOperatorFormsGammaH.html#L36), that is the reduced diamond $\langle p \rangle$; and a finite set $SS$ of pairs of places of $\overline F$ which by $hSS$ is exactly `ssNodePairsQExp κ (JHNeronObjectAtP.ΓN p M H hpM) p`, the set of pairs $s$ with $s.2$ supersingular and $s.1$ the Frobenius image `qExpFrobeniusPlaceModL` of $s.2$.
--
--   Further, $Psp$ is a term of `JHPlaceSpecialization p M H hpM A`, which packages a specialisation map `sp` from places of $F_{M/p}$ over $\overline{\mathbb Q}$ to places of $\overline F$ over $\kappa$, a homomorphism on degree-zero divisor classes, and the compatibility clauses of that structure ($q$-expansion compatibility of divisor push-forward, surjectivity of `sp`, existence of a reduced function with the pushed-forward principal divisor, invariance under inertia and Frobenius-equivariance of `sp` for the arithmetic Galois action, and compatibility of the two maps on $\mathrm{Pic}^0$). $Rpd$ is a `ProlongationDatum Psp θ`, consisting of two regular prolongations $R_1, R_2$ of $A$ from $\overline{\mathbb Q}$ to $F_M$ with residue maps to $\overline F$, the clause `residue₁_coeffMap` expressing that $R_1$ computes residues coefficientwise on Laurent series with coefficients in $A$, and the clauses identifying the $R_2$-integers and $R_2$-residues with the $R_1$-integers and $R_1$-residues of $\theta$-translates. For a place $W$ of $F_M$, `reduceFst α hα W` is `sp` applied to the restriction of $W$ along $\alpha$, and `reduceSnd β hβ δ W` is $\delta$ applied to `sp` of the restriction of $W$ along $\beta$; $W$ is strict of the first kind (`IsStrictFst`) when $\delta$ of the Frobenius image of `reduceFst W` equals `reduceSnd W` and `reduceFst W` is not `Fixed` for $\delta$, and strict of the second kind (`IsStrictSnd`) when `reduceFst W` is the Frobenius image of `reduceSnd W` and `reduceSnd W` is not `Fixed`.
--
--   The structural laws assumed are: $hTD$ (`TypeDichotomy`), that every place $W$ of $F_M$ satisfies at least one of the two equalities above; $hmodel$ (`IsModel`), the conjunction of the two divisor laws — for $f$ integral for both prolongations with nonzero residues and $D$ the divisor of $f$, the push-forward along `reduceFst` of the strict-first part of $D$ at a non-fixed place $v$ is $v(\mathrm{res}_1 f)$, and symmetrically for the strict-second part, `reduceSnd` and $\mathrm{res}_2 f$ — together with the two cusp laws, which compute the push-forwards of the infinity-side part of $D$ along `reduceFst` and of the zero-side part along `reduceSnd` at the images of infinity-side resp. zero-side places in terms of the orders of $\mathrm{res}_1 f$, $\mathrm{res}_2 f$; $hO$ (`OrderLawFixed`), that at a fixed affine place $v$ the push-forward of $D$ along `reduceFst` equals $v(\mathrm{res}_1 f) + (\delta(\mathrm{Frob}\, v))(\mathrm{res}_2 f)$; $hRL$ (`RegularityLaw` for $SS$, two clauses), that absence of poles above a fixed affine place forces non-negativity of the two residue orders, and that absence of poles above $s.1$ for $s \in SS$ yields a common value $c \in \kappa$ of $\mathrm{res}_1 f$ at $s.1$ and $\mathrm{res}_2 f$ at $s.2$; and $hNV$ (`NodeValueLaw` for $SS$), that if no place $V$ with $V(f) \neq 0$ reduces to the pair $s \in SS$ then $\mathrm{res}_1 f$ and $\mathrm{res}_2 f$ take one and the same nonzero value at $s.1$ and $s.2$.
--
--   The normalisation hypotheses are $h\alpha\_coe$, that $\alpha$ is the identity on $q$-expansions, and $h\beta\_coe$, that $\beta$ is the substitution $q \mapsto q^p$, i.e. the $q$-expansion of $\beta u$ is `qExpand` at $p$ of that of $u$; $h\theta gal$, that $\theta$ commutes with the arithmetic Galois action of $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ on $F_M$; and $h\beta\theta$, that $\beta$ is $\alpha$ followed by $\theta$.
--
--   Two pole-bound hypotheses are assumed, $hLFst$ and $hLSnd$, mirror images of one another. The first requires: for all places $Q \neq Q'$ of $F_M$, both strict of the first kind and with the same image under `reduceFst`, that image being an affine place (`IsAffinePlace`, i.e. the reduced modular invariant has a finite value there), for every natural $n$ with $n \neq 0$ in $\kappa$, every $g$ in the $R_1$-integers with nonzero $R_1$-residue such that $Q(g) = -n$, $Q'(g) = n$ and $W(g) = 0$ for every other strict first-kind place $W$ with the same `reduceFst`-image, and every $e \in A$ and every $\varepsilon$ in the $R_1$-integers with nonzero residue such that $g = 1 + e\,\varepsilon$: the order of $\mathrm{res}_1 \varepsilon$ at `reduceFst Q` is at least $-1$. The hypothesis $hLSnd$ is the same statement with `IsStrictSnd`, `reduceSnd` and $R_2$ throughout.
--
--   The hypothesis $hUnit$ asserts the existence of $u_1, u_2 \in F_M$ and divisors $D_1, D_2$ on $F_M$ with $D_i$ the divisor of $u_i$, such that: $u_1$ and $u_1^{-1}$ are $R_1$-integral with $\mathrm{res}_1 u_1 \neq 0$, the push-forward along `reduceFst` of the strict-first part of $D_1$ at any non-fixed place $v$ equals $v(\mathrm{res}_1 u_1)$, and the push-forward along `reduceFst` of the infinity-side part of $D_1$ at `reduceFst C` equals $(\mathrm{reduceFst}\, C)(\mathrm{res}_1 u_1)$ for every infinity-side place $C$; every nonzero $f \in F_M$ admits $m \neq 0$ in $\mathbb N$ and $j \in \mathbb Z$ with $f^m u_1^{\,j}$ $R_2$-integral of nonzero $R_2$-residue; and the two symmetric clauses for $u_2$, with $R_2$, `reduceSnd`, the strict-second part of $D_2$, the zero-side part of $D_2$, and with $f^m u_2^{\,j}$ $R_1$-integral of nonzero $R_1$-residue. The hypothesis $hcusp$ asserts that every non-affine place $w$ of $\overline F$ is the `reduceFst`-image of some infinity-side place and the `reduceSnd`-image of some zero-side place.
--
--   Finally, let $Q_s$ be a place of $F_M$ strict of the first kind, and let $r \in F_M$ be integral for $R_1$ (witness $h_1$) and have no poles above the first reading of $Q_s$: $0 \le V(r)$ for every strict first-kind place $V$ with `reduceFst V = reduceFst Qs` (hypothesis $hr$).
--
--   The conclusion is that there exists $c \in A$ such that, first, $Q_s$ has value the image of $c$ in $\overline{\mathbb Q}$ at $r$, that is $r$ lies in the valuation ring of $Q_s$ and its residue there is the image of $c$ under the structure map $\overline{\mathbb Q} \to$ `Qs.ResidueField`; and, second, the place `reduceFst α hα Qs` has value `IsLocalRing.residue ↥A c` at the $R_1$-residue of $r$, that is $\mathrm{res}_1 r$ lies in the valuation ring of that place of $\overline F$ and its residue there is the image of $c \bmod \mathfrak m_A$ under the structure map from $\kappa$.
--
--   This is the value law of Deuring-style reduction theory in the present setting: a function integral for the first Gauss prolongation and without poles along the first component above a given place acquires a value in $A$ at a strict place of the first kind, and that value reduces to the value of its residue function on the characteristic-$p$ fibre. It is invoked in the divisor computations on the reduction of $X_H(M)$ at a prime $p$ exactly dividing $M$, namely in [`ModularCurve.JHPlaceSpecialization.ProlongationDatum.IsModel.sum_single_add_sum_single_eq_of_ord_eq_nsmul_sub_of_gammaLift_of_discLaw_of_unit_of_cusp`](thm.html#ModularCurve.JHPlaceSpecialization.ProlongationDatum.IsModel.sum_single_add_sum_single_eq_of_ord_eq_nsmul_sub_of_gammaLift_of_discLaw_of_unit_of_cusp) and [`ModularCurve.JHPlaceSpecialization.ProlongationDatum.sum_single_add_sum_single_eq_of_ord_eq_nsmul_sub_of_residue_eq_one_of_hasValue_one_of_discLaw_of_cusp`](thm.html#ModularCurve.JHPlaceSpecialization.ProlongationDatum.sum_single_add_sum_single_eq_of_ord_eq_nsmul_sub_of_residue_eq_one_of_hasValue_one_of_discLaw_of_cusp).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHPlaceSpecialization_ProlongationDatum_IsModel_exists_hasValue_and_hasValue_residue_reduceFst_of_isStrictFst_of_forall_ord_nonneg_of_unit_of_cusp.lean

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

theorem ModularCurve.JHPlaceSpecialization.ProlongationDatum.IsModel.exists_hasValue_and_hasValue_residue_reduceFst_of_isStrictFst_of_forall_ord_nonneg_of_unit_of_cusp
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

    (Qs : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (hQs : Psp.IsStrictFst α β hα hβ δ Qs)
    (r : ↥(xHFunctionFieldBar M H)) (h₁ : r ∈ Rpd.R₁.integers)
    (hr : ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.IsStrictFst α β hα hβ δ V →
      Psp.reduceFst α hα V = Psp.reduceFst α hα Qs → 0 ≤ V.ord r) :
    ∃ c : ↥A, Qs.HasValue r (c : AlgebraicClosure ℚ) ∧
      (Psp.reduceFst α hα Qs).HasValue (Rpd.R₁.residue ⟨r, h₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) (IsLocalRing.residue ↥A c) := by sorry
