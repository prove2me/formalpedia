-- Prove2me | Theorems.Thm_ModularCurve_JHPlaceSpecialization_exists_isPrincipal_apply_eq_neg_one_forall_support_good_of_isInftySide_or_isStrictFst
-- name    : ModularCurve.JHPlaceSpecialization.exists_isPrincipal_apply_eq_neg_one_forall_support_good_of_isInftySide_or_isStrictFst
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/9e53c56d-5f37-51f9-b00a-1f20accc55b8
-- title:
--   Removing a bad place of the first kind on X_H(M)
-- statement:
--   Setting. Fixed are a prime $p$ and a modulus $M$ with $p \mid M$ (`hpM`) and $p^2 \nmid M$ (`hpM2`), a subgroup $H \le (\mathbb Z/M)^\times$ containing every unit whose image under the reduction $(\mathbb Z/M)^\times \to (\mathbb Z/(M/p))^\times$ is $1$ (`hHp`), and a valuation subring $A$ of $\overline{\mathbb Q}$ with $p$ a non-unit of $A$ (`hA`, the predicate `LiesOverPrime`), whose residue field $\kappa =$ `ResidueField ↥A` is algebraically closed of characteristic $p$. Write $F$ for `↥(xHFunctionFieldBar M H)`, the base change to $\overline{\mathbb Q}$ of the $q$-expansion function field of $X_H(M)$ inside Laurent series, $F'$ for `↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))`, the analogous field at level $M/p$ for the image subgroup `infSubgroup p M H hpM`, and $\bar F$ for `JHNeronObjectAtP.Fbar p M H hpM` $\kappa$, the $q$-expansion function field over $\kappa$ attached to `JHNeronObjectAtP.ΓN p M H hpM`. Throughout, $\operatorname{ord}_V$ is the order function of a place, $\mathrm{Frob}$ denotes `qExpFrobeniusPlaceModL` $\kappa$ `(JHNeronObjectAtP.ΓN p M H hpM)` $p$ (restriction of a place along the mod-$p$ Frobenius of the $q$-expansion field), and a place $v$ of $\bar F$ is called fixed when $\mathrm{Frob}(\delta(\mathrm{Frob}\,v)) = v$ (the predicate `Fixed`) and affine when some $x \in \bar F$ with Laurent expansion `jqModC` $\kappa$ has a value in $\kappa$ at $v$ (the predicate `IsAffinePlace`).
--
--   Degeneracy data. Given are an automorphism $\theta$ of $F$ over $\overline{\mathbb Q}$ and two integral $\overline{\mathbb Q}$-algebra maps $\alpha, \beta : F' \to F$ (`hα`, `hβ`), subject to: `hα_coe`, that $\alpha$ preserves Laurent expansions; `hβ_coe`, that the expansion of $\beta u$ is the expansion of $u$ substituted through `qExpand` $\overline{\mathbb Q}$ $p$ (that is, $q \mapsto q^p$); `hβθ`, that $\beta$ is $\alpha$ followed by $\theta$; and `hθgal`, that $\theta$ commutes with the coefficientwise action `arithmeticGalois` of every $\sigma \in \mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ on $F$. Further, $pb$ is a unit of $\mathbb Z/(M/p)$ whose underlying element is $p$ (`hpb`), and $\delta$ is a self-map of the places of $\bar F$ which, by `hδ`, is the action on places of the semilinear automorphism `SemilinearAut.ofAlgAut` attached to the diamond automorphism `diamondActionModL` $\kappa$ $(M/p)$ `(infSubgroup p M H hpM)` `(CuspForm.gammaLift (M / p) pb)`. Finally, $SS$ is a finite set of pairs of places of $\bar F$ which, by `hSS`, is exactly `ssNodePairsQExp` $\kappa$ `(JHNeronObjectAtP.ΓN p M H hpM)` $p$: the pairs $(s_1, s_2)$ with $s_2$ a supersingular place and $s_1 = \mathrm{Frob}\,s_2$.
--
--   Specialisation and prolongation. `Psp` is a `JHPlaceSpecialization` for $(p, M, H, hpM, A)$: a map `sp` from places of $F'$ to places of $\bar F$ together with a homomorphism on degree-zero divisor classes, satisfying the compatibilities listed in that structure ($q$-expansion compatibility of divisors, surjectivity, the inertia and Frobenius laws for the arithmetic Galois action, and compatibility with $\mathrm{Pic}^0$). For a place $W$ of $F$ one writes $\mathrm{red}_1 W =$ `Psp.reduceFst α hα` $W =$ `sp`$(W|_\alpha)$ and $\mathrm{red}_2 W =$ `Psp.reduceSnd β hβ δ` $W = \delta($`sp`$(W|_\beta))$; the place $W$ is strict of the first kind (`IsStrictFst`) when $\delta(\mathrm{Frob}(\mathrm{red}_1 W)) = \mathrm{red}_2 W$ and $\mathrm{red}_1 W$ is not fixed, and strict of the second kind (`IsStrictSnd`) when $\mathrm{red}_1 W = \mathrm{Frob}(\mathrm{red}_2 W)$ and $\mathrm{red}_2 W$ is not fixed. `Rpd` is a `ProlongationDatum` for `Psp` and $\theta$: two regular prolongations $R_1, R_2$ of $A$ to $F$ with residue maps to $\bar F$, the $q$-expansion formula for the residue of $R_1$, and the identifications $f \in R_2$ iff $\theta f \in R_1$ together with $R_2$-residue of $f$ equal to $R_1$-residue of $\theta f$.
--
--   The law block. The hypotheses `hTD`, `hFix`, `hmodel`, `hO`, `hRL`, `hNV` require: (`hTD`) for every place $W$ of $F$, either $\mathrm{red}_1 W = \mathrm{Frob}(\mathrm{red}_2 W)$ or $\delta(\mathrm{Frob}(\mathrm{red}_1 W)) = \mathrm{red}_2 W$; (`hFix`) the set of fixed places of $\bar F$ is finite; (`hmodel`) the conjunction `IsModel` of the two divisor laws `DivisorLawFst`, `DivisorLawSnd` — for $f$ lying in both $R_1$ and $R_2$ with both residues non-zero and $D$ the divisor of $f$, the pushforward along $\mathrm{red}_1$ of the part of $D$ supported on strict-first places takes, at each non-fixed place $v$, the value $\operatorname{ord}_v$ of the $R_1$-residue of $f$, and symmetrically for strict-second places, $\mathrm{red}_2$ and $R_2$ — together with the cusp law `CuspLawInfty` (the same comparison for the part of $D$ supported on $\infty$-side places, evaluated at $\mathrm{red}_1$ of an $\infty$-side place) and its zero-side counterpart `CuspLawZero`; (`hO`) the law `OrderLawFixed`: for such $f$ and $D$ and every fixed affine place $v$, the pushforward of $D$ along $\mathrm{red}_1$ at $v$ equals $\operatorname{ord}_v$ of the $R_1$-residue plus $\operatorname{ord}_{\delta(\mathrm{Frob}\,v)}$ of the $R_2$-residue; (`hRL`) the two clauses of `RegularityLaw` relative to $SS$, namely non-negativity of the two residue orders at a fixed affine place $v$ whenever $f$ has non-negative order at all places above $v$, and, for $s \in SS$ with $f$ of non-negative order at all places above $s_1$, the existence of $c \in \kappa$ which is the value of the $R_1$-residue at $s_1$ and of the $R_2$-residue at $s_2$; (`hNV`) the law `NodeValueLaw` relative to $SS$: for $f$ as above and $s \in SS$ such that no place $V$ with $\operatorname{ord}_V f \ne 0$ satisfies $(\mathrm{red}_1 V, \mathrm{red}_2 V) = s$, there is a non-zero $c \in \kappa$ that is simultaneously the value of the $R_1$-residue at $s_1$ and of the $R_2$-residue at $s_2$.
--
--   Local order bounds. The hypothesis `hLFst` requires, for all places $Q \neq Q'$ of $F$ that are strict of the first kind with $\mathrm{red}_1 Q' = \mathrm{red}_1 Q$ and $\mathrm{red}_1 Q$ affine, for every $n \in \mathbb N$ whose image in $\kappa$ is non-zero, every $g \in R_1$ with non-zero $R_1$-residue such that $\operatorname{ord}_Q g = -n$, $\operatorname{ord}_{Q'} g = n$ and $\operatorname{ord}_W g = 0$ for every further strict-first place $W$ with $\mathrm{red}_1 W = \mathrm{red}_1 Q$, and every $e \in A$ and $\varepsilon \in R_1$ with non-zero $R_1$-residue such that $g = 1 + e\varepsilon$: that $\operatorname{ord}_{\mathrm{red}_1 Q}$ of the $R_1$-residue of $\varepsilon$ be at least $-1$. The hypothesis `hLSnd` is the same statement with strict-first replaced by strict-second, $\mathrm{red}_1$ by $\mathrm{red}_2$ and $R_1$ by $R_2$.
--
--   Common units. The hypothesis `hUnit` asserts the existence of $u_1, u_2 \in F$ and divisors $D_1, D_2$ with $D_i(W) = \operatorname{ord}_W u_i$ for all $W$, such that: $u_1$ and $u_1^{-1}$ lie in $R_1$, the $R_1$-residue of $u_1$ is non-zero, the pushforward along $\mathrm{red}_1$ of the strict-first part of $D_1$ takes at every non-fixed place $v$ the value $\operatorname{ord}_v$ of that residue, and the pushforward along $\mathrm{red}_1$ of the $\infty$-side part of $D_1$ takes at $\mathrm{red}_1 C$, for every $\infty$-side place $C$, the value $\operatorname{ord}_{\mathrm{red}_1 C}$ of that residue; every non-zero $f \in F$ admits $m \neq 0$ in $\mathbb N$ and $j \in \mathbb Z$ with $f^m u_1^{j} \in R_2$ of non-zero $R_2$-residue; and symmetrically for $u_2$, with $R_2$, $\mathrm{red}_2$, the strict-second part of $D_2$ and the zero-side part of $D_2$, every non-zero $f$ admitting $m \neq 0$ and $j$ with $f^m u_2^{j} \in R_1$ of non-zero $R_1$-residue. Here the $\infty$-side and zero-side conditions are the predicates `IsInftySide` and `IsZeroSide` on places of $F$ (cuspidality for $j$, respectively for $j$ in the $p$-fold $q$-expansion, together with the prescribed value $1$ in the residue field for the relevant ratio of the two $j$'s).
--
--   Cusps and orientation. The hypothesis `hcusp` requires every non-affine place $w$ of $\bar F$ to be $\mathrm{red}_1$ of some $\infty$-side place and $\mathrm{red}_2$ of some zero-side place; `horientInf` requires $\delta(\mathrm{Frob}(\mathrm{red}_1 C)) = \mathrm{red}_2 C$ for every $\infty$-side place $C$, and `horient0` requires $\mathrm{red}_1 C = \mathrm{Frob}(\mathrm{red}_2 C)$ for every zero-side place $C$.
--
--   Modular invariants and the bad place. Given are a finite set $S \subseteq \kappa$ none of whose elements lies in `ssJSet` $p$ $\kappa$, the set of $j \in \kappa$ such that every elliptic Weierstrass curve over $\kappa$ with invariant $j$ has only the zero point killed by $p$ (`hS`); an element $xj \in F$ with Laurent expansion `jqModC` $\overline{\mathbb Q}$ (`hxj`) and an element $xb \in \bar F$ with Laurent expansion `jqModC` $\kappa$ (`hxb`); a finite set $T$ of places of $\bar F$ containing every place $t$ at which $xb$ fails to be integral or for which $\operatorname{ord}_t(xb - s) > 0$ for some $s \in S$ (`hT`); and a place $V_0$ of $F$ which is bad, in the sense that there is no $a \in A$ with $\operatorname{ord}_{V_0}(xj - a) > 0$ and the residue of $a$ in $\kappa$ outside $S$ (`hbad`), and which by `hside` is either on the $\infty$-side or strict of the first kind.
--
--   Conclusion. Under these hypotheses there exists a divisor $p'$ on $F$ over $\overline{\mathbb Q}$ such that: $p'$ is principal, that is, $p'(V) = \operatorname{ord}_V f$ for all places $V$ for some non-zero $f \in F$; $p'(V_0) = -1$; the degree of $p'$ is $0$; and every $V$ in the support of $p'$ other than $V_0$ is good, that is, there is $a \in A$ with $\operatorname{ord}_V(xj - a) > 0$ whose residue in $\kappa$ does not lie in $S$.
--
--   This is the first-kind half of the step that removes a single bad point from a divisor on $X_H(M)$ at a prime $p$ exactly dividing $M$: it produces a principal degree-zero divisor with a simple pole at the given bad place $V_0$ and all remaining support at places where the $j$-invariant specialises to a prescribed non-supersingular residue. Combined with the second-kind half (the $0$-side or strict-second branch), it yields the unconditional removal statement [`ModularCurve.JHPlaceSpecialization.exists_isPrincipal_apply_eq_neg_one_forall_support_good_of_isInftySide_or_isStrictFst_or_isZeroSide_or_isStrictSnd`](thm.html#ModularCurve.JHPlaceSpecialization.exists_isPrincipal_apply_eq_neg_one_forall_support_good_of_isInftySide_or_isStrictFst_or_isZeroSide_or_isStrictSnd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHPlaceSpecialization_exists_isPrincipal_apply_eq_neg_one_forall_support_good_of_isInftySide_or_isStrictFst.lean

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

theorem ModularCurve.JHPlaceSpecialization.exists_isPrincipal_apply_eq_neg_one_forall_support_good_of_isInftySide_or_isStrictFst
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
    (hside : JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A) V₀ ∨ Psp.IsStrictFst α β hα hβ δ V₀) :
    ∃ p' : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
      Divisor.IsPrincipal p' ∧ p' V₀ = -1 ∧ Divisor.degree p' = 0 ∧
        ∀ V ∈ p'.support, V ≠ V₀ → (∃ a : ↥A, 0 < V.ord (xj - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a : AlgebraicClosure ℚ)) ∧ IsLocalRing.residue ↥A a ∉ S) := by sorry
