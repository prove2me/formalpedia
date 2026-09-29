-- Prove2me | Theorems.Thm_ModularCurve_JHPlaceSpecialization_exists_isPrincipal_apply_eq_neg_one_forall_support_good_of_fixed_of_isAffinePlace
-- name    : ModularCurve.JHPlaceSpecialization.exists_isPrincipal_apply_eq_neg_one_forall_support_good_of_fixed_of_isAffinePlace
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/d66c6606-706f-5838-851a-1cb6fa518233
-- title:
--   Removing a bad place with fixed affine first reduction
-- statement:
--   Throughout, $p$ is a prime and $M$ a positive integer with $p \mid M$ but $p^2 \nmid M$, and $H \le (\mathbb{Z}/M)^\times$ is a subgroup containing every unit that reduces to $1$ in $(\mathbb{Z}/(M/p))^\times$ (hypothesis `hHp`). Write $F_M$ for `xHFunctionFieldBar M H`, the base change to $\overline{\mathbb{Q}}$ of the $q$-expansion function field `xHFunctionField M H` inside $\overline{\mathbb{Q}}((q))$, and $F_{M/p}$ for the corresponding field at level $M/p$ with group `infSubgroup p M H hpM`, the image of $H$ under $(\mathbb{Z}/M)^\times \to (\mathbb{Z}/(M/p))^\times$. Further, $A$ is a valuation subring of $\overline{\mathbb{Q}}$ lying over $p$ in the sense that $p$ is a non-unit of $A$, with residue field $\kappa =$ `ResidueField ↥A` algebraically closed of characteristic $p$; $F_b$ denotes `JHNeronObjectAtP.Fbar p M H hpM κ`, the characteristic-$p$ $q$-expansion function field of the group `JHNeronObjectAtP.ΓN p M H hpM`. A place of a field extension is, as in `Place`, a valuation subring containing the base field, different from the whole field and a principal ideal ring; `ord` is the associated additive valuation, `Divisor` the group of finitely supported $\mathbb{Z}$-valued functions on places, and `HasValue g a` means that $g$ lies in the valuation ring and has residue the image of $a$.
--
--   The geometric frame consists of: an $\overline{\mathbb{Q}}$-algebra automorphism $\theta$ of $F_M$; two integral $\overline{\mathbb{Q}}$-algebra maps $\alpha, \beta : F_{M/p} \to F_M$ (hypotheses `hα`, `hβ`), pinned on $q$-expansions by `hα_coe` (the $q$-expansion of $\alpha u$ is that of $u$) and `hβ_coe` (the $q$-expansion of $\beta u$ is obtained from that of $u$ by `qExpand` at $p$, i.e. $q \mapsto q^p$), and related by `hβθ`: $\beta = \theta \circ \alpha$; a unit $pb$ of $\mathbb{Z}/(M/p)$ whose underlying element is $p$ (`hpb`); a self-map $\delta$ of the places of $F_b$ which, by `hδ`, is the action on places of the semilinear automorphism attached to the diamond automorphism `diamondActionModL` of the lift [`CuspForm.gammaLift (M / p) pb`](def/CuspForm_HeckeOperatorFormsGammaH.html#L36); a finite set $SS$ of pairs of places of $F_b$ which, by `hSS`, is exactly `ssNodePairsQExp`, the set of pairs $(\mathrm{Frob}(v), v)$ with $v$ a supersingular place, $\mathrm{Frob}$ being `qExpFrobeniusPlaceModL`; a specialisation datum $P_{sp} =$ `JHPlaceSpecialization p M H hpM A`, consisting of a surjective map $\mathrm{sp}$ from places of $F_{M/p}$ to places of $F_b$ together with a map on degree-zero divisor classes, compatible with $q$-expansion reductions, with divisors of functions, and with inertia and Frobenius in the arithmetic Galois action; and a prolongation datum $R_{pd}$ for $P_{sp}$ and $\theta$, given by two regular prolongations $R_1, R_2$ of $A$ from $F_M$ to $F_b$ whose residue maps compute reductions of $q$-expansions and satisfy $f \in R_2.\mathrm{integers} \iff \theta f \in R_1.\mathrm{integers}$ and $R_2.\mathrm{residue}(f) = R_1.\mathrm{residue}(\theta f)$. Here $\mathrm{red}_1 W = \mathrm{sp}(W|_\alpha)$ is `reduceFst` and $\mathrm{red}_2 W = \delta(\mathrm{sp}(W|_\beta))$ is `reduceSnd`; a place $v$ of $F_b$ is `Fixed` for $\delta$ when $\mathrm{Frob}(\delta(\mathrm{Frob}(v))) = v$, and is an `IsAffinePlace` when the element of $F_b$ with $q$-expansion `jqModC` lies in its valuation ring with residue in $\kappa$.
--
--   The law block comprises: `hTD`, the type dichotomy, asserting that every place $W$ of $F_M$ satisfies $\mathrm{red}_1 W = \mathrm{Frob}(\mathrm{red}_2 W)$ or $\delta(\mathrm{Frob}(\mathrm{red}_1 W)) = \mathrm{red}_2 W$; `hFix`, the finiteness of the set of $\delta$-fixed places of $F_b$; `hmodel`, the four divisor laws `DivisorLawFst`, `DivisorLawSnd`, `CuspLawInfty`, `CuspLawZero` for $R_{pd}$ (for $f$ with non-zero residues in both prolongations, the pushforward along $\mathrm{red}_1$ of the part of $\mathrm{div}(f)$ carried by strictly-first places computes $\mathrm{ord}_v$ of the first residue of $f$ at non-fixed $v$, and symmetrically, together with the cusp-side counterparts); `hO`, `OrderLawFixed`, which at a fixed affine place $v$ computes the full pushforward of $\mathrm{div}(f)$ as $\mathrm{ord}_v$ of the first residue plus $\mathrm{ord}_{\delta(\mathrm{Frob}(v))}$ of the second; `hRL`, `RegularityLaw` for $SS$ (two clauses: non-negativity of the residue orders at fixed affine places, and existence of a common value at supersingular node pairs, under the corresponding non-negativity of $\mathrm{ord}_V f$); `hNV`, `NodeValueLaw` for $SS$ (at a node pair missed by $\mathrm{div}(f)$ the two residues take a common non-zero value); and `hθgal`, the commutation of $\theta$ with the arithmetic Galois action of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ on coefficients.
--
--   Two local binders `hLFst` and `hLSnd` are assumed, in mirror-image form. `hLFst` requires: for all places $Q \ne Q'$ of $F_M$ that are strictly first (in the sense of `IsStrictFst`) with $\mathrm{red}_1 Q' = \mathrm{red}_1 Q$ an affine place, for every natural $n$ whose image in $\kappa$ is non-zero, for every $g \in R_1.\mathrm{integers}$ with non-zero first residue such that $\mathrm{ord}_Q g = -n$, $\mathrm{ord}_{Q'} g = n$ and $\mathrm{ord}_W g = 0$ for every other strictly-first $W$ with the same first reduction, and for every $e \in A$ and $\varepsilon \in R_1.\mathrm{integers}$ with non-zero first residue such that $g = 1 + e\,\varepsilon$, one has $\mathrm{ord}_{\mathrm{red}_1 Q}$ of the first residue of $\varepsilon$ at least $-1$. `hLSnd` is the same statement with `IsStrictSnd`, $\mathrm{red}_2$ and $R_2$ in place of `IsStrictFst`, $\mathrm{red}_1$ and $R_1$.
--
--   The modular-unit clause `hUnit` asserts the existence of $u_1, u_2 \in F_M$ and divisors $D_1, D_2$ with $D_i(W) = \mathrm{ord}_W u_i$ for all $W$, such that: $u_1$ and $u_1^{-1}$ lie in $R_1.\mathrm{integers}$ with non-zero first residue, the pushforward along $\mathrm{red}_1$ of the strictly-first part of $D_1$ agrees with $\mathrm{ord}_v$ of the first residue of $u_1$ at every non-fixed $v$, and the pushforward along $\mathrm{red}_1$ of the infinity-side part of $D_1$ agrees at $\mathrm{red}_1 C$ with $\mathrm{ord}_{\mathrm{red}_1 C}$ of that residue for every infinity-side $C$; that for every $f \ne 0$ there are $m \ne 0$ and $j \in \mathbb{Z}$ with $f^m u_1^{j} \in R_2.\mathrm{integers}$ of non-zero second residue; and the mirror statements for $u_2$, $D_2$, $R_2$, $\mathrm{red}_2$, the strictly-second part, the zero-side cusps, and $f^m u_2^{j} \in R_1.\mathrm{integers}$. Here infinity-side and zero-side places are as in `IsInftySide` and `IsZeroSide`: cuspidal for $j$ respectively for $j(q^p)$, and carrying a value with residue $1$ on $x'/x^p$ respectively $x/x'^p$, where $x$, $x'$ have $q$-expansions `jqModC` and its `qExpand` at $p$.
--
--   The cusp-fibre clause `hcusp` requires every non-affine place $w$ of $F_b$ to be both $\mathrm{red}_1 C$ for some infinity-side $C$ and $\mathrm{red}_2 C$ for some zero-side $C$. The two orientation clauses require $\delta(\mathrm{Frob}(\mathrm{red}_1 C)) = \mathrm{red}_2 C$ for every infinity-side $C$ (`horientInf`) and $\mathrm{red}_1 C = \mathrm{Frob}(\mathrm{red}_2 C)$ for every zero-side $C$ (`horient0`).
--
--   Finally, the data specific to this statement: a finite set $S \subseteq \kappa$ none of whose elements lies in `ssJSet p κ`, that is, each $s \in S$ admits an elliptic curve over $\kappa$ with invariant $s$ having a non-zero $p$-torsion point (so $S$ avoids the supersingular invariants); an element $xj \in F_M$ whose $q$-expansion is `jqModC` over $\overline{\mathbb{Q}}$, and $xb \in F_b$ whose $q$-expansion is `jqModC` over $\kappa$; a finite set $T$ of places of $F_b$ containing every place $t$ at which $xb$ fails to lie in the valuation ring or at which $\mathrm{ord}_t(xb - s) > 0$ for some $s \in S$ (`hT`); and a place $V_0$ of $F_M$ which is bad, in the sense of `hbad`: there is no $a \in A$ with $\mathrm{ord}_{V_0}(xj - a) > 0$ and residue of $a$ outside $S$. It is assumed that $\mathrm{red}_1 V_0$ is $\delta$-fixed (`hfix`) and is an affine place (`haff`).
--
--   Under these hypotheses there exists a divisor $p'$ of $F_M$ over $\overline{\mathbb{Q}}$ such that: $p'$ is principal, i.e. there is $f \ne 0$ in $F_M$ with $p'(V) = \mathrm{ord}_V f$ for all places $V$; $p'(V_0) = -1$; the degree of $p'$ is $0$; and every $V$ in the support of $p'$ other than $V_0$ is good, i.e. there is $a \in A$ with $\mathrm{ord}_V(xj - a) > 0$ and residue of $a$ not in $S$.
--
--   This is the avoidance step of the place-specialisation analysis on $X_H(M)$ at a prime $p$ exactly dividing the level: a single bad place whose first reduction is a $\delta$-fixed affine place of the characteristic-$p$ fibre can be cancelled by a principal degree-zero divisor whose remaining support consists of places where the modular invariant specialises to a residue outside the excluded set $S$. It is the fixed-affine case feeding the companion result [`ModularCurve.JHPlaceSpecialization.exists_isPrincipal_apply_eq_neg_one_forall_support_good_of_not_good_of_coe_of_unit_of_cusp_of_orient`](thm.html#ModularCurve.JHPlaceSpecialization.exists_isPrincipal_apply_eq_neg_one_forall_support_good_of_not_good_of_coe_of_unit_of_cusp_of_orient), which assembles the cases into a removal statement for arbitrary bad places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHPlaceSpecialization_exists_isPrincipal_apply_eq_neg_one_forall_support_good_of_fixed_of_isAffinePlace.lean

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
set_option maxHeartbeats 500000 in

theorem ModularCurve.JHPlaceSpecialization.exists_isPrincipal_apply_eq_neg_one_forall_support_good_of_fixed_of_isAffinePlace
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
    (xb : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) (hxb : ((xb : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A)) = jqModC (ResidueField ↥A))

    (T : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (hT : ∀ t : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), (xb ∉ t.toValuationSubring ∨ ∃ s ∈ S, 0 < t.ord (xb - algebraMap (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) s)) → t ∈ T)
    (V₀ : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (hbad : ¬ (∃ a : ↥A, 0 < V₀.ord (xj - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a : AlgebraicClosure ℚ)) ∧ IsLocalRing.residue ↥A a ∉ S))
    (hfix : JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ (Psp.reduceFst α hα V₀))
    (haff : JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A) (Psp.reduceFst α hα V₀)) :
    ∃ p' : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
      Divisor.IsPrincipal p' ∧ p' V₀ = -1 ∧ Divisor.degree p' = 0 ∧
        ∀ V ∈ p'.support, V ≠ V₀ → (∃ a : ↥A, 0 < V.ord (xj - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a : AlgebraicClosure ℚ)) ∧ IsLocalRing.residue ↥A a ∉ S) := by sorry
