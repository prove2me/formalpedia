-- Prove2me | Theorems.Thm_ModularCurve_JHPlaceSpecialization_ProlongationDatum_residue_fst_box_and_residue_snd_box_and_node_hasValue_of_mem_riemannRochSpace
-- name    : ModularCurve.JHPlaceSpecialization.ProlongationDatum.residue_fst_box_and_residue_snd_box_and_node_hasValue_of_mem_riemannRochSpace
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/ff53693d-7fb5-56e8-89e3-52231c8bc5eb
-- title:
--   Residue bounds and node values for bi-integral Riemann–Roch sections
-- statement:
--   Throughout, $p$ is a prime and $M \neq 0$ with $p \mid M$ (`hpM`) and $p^2 \nmid M$ (`hpM2`); $H \le (\mathbb{Z}/M)^\times$ is a subgroup containing every unit which reduces to $1$ in $(\mathbb{Z}/(M/p))^\times$ (`hHp`); and $A$ is a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $A$ (`hA`, i.e. `LiesOverPrime p`), whose residue field $\kappa =$ `ResidueField ↥A` is of characteristic $p$ and algebraically closed. Write $F_M =$ `xHFunctionFieldBar M H` for the base change to $\overline{\mathbb{Q}}$ of the $q$-expansion function field of $X_H(M)$, $F' =$ `xHFunctionFieldBar (M/p) (infSubgroup p M H hpM)` for the corresponding field at level $M/p$ with group the image of $H$ in $(\mathbb{Z}/(M/p))^\times$, and $\bar F =$ `JHNeronObjectAtP.Fbar p M H hpM κ` for the $\kappa$-function field attached to `JHNeronObjectAtP.ΓN p M H hpM`. Places are places in the sense of `Place` (valuation subrings containing the constants, proper, with principal maximal ideal), $\operatorname{ord}_v$ is the associated normalised valuation, $v.\mathrm{HasValue}\,g\,a$ means that $g$ lies in the valuation ring of $v$ and has residue the image of $a$, and $\varphi =$ `qExpFrobeniusPlaceModL κ (ΓN p M H hpM) p` is restriction of places along the mod-$p$ Frobenius on $\bar F$.
--
--   The data are: an automorphism $\theta$ of $F_M$ over $\overline{\mathbb{Q}}$; two $\overline{\mathbb{Q}}$-algebra maps $\alpha, \beta : F' \to F_M$, both integral (`hα`, `hβ`); a unit $pb$ of $\mathbb{Z}/(M/p)$ whose underlying residue is $p$ (`hpb`); a self-map $\delta$ of the places of $\bar F$ which by `hδ` is the action on places of the semilinear automorphism attached to the diamond automorphism `diamondActionModL κ (M/p) (infSubgroup p M H hpM)` evaluated at the lift [`CuspForm.gammaLift (M/p) pb`](def/CuspForm_HeckeOperatorFormsGammaH.html#L36); a finset $SS$ of pairs of places of $\bar F$ which by `hSS` is exactly `ssNodePairsQExp κ (ΓN p M H hpM) p`, the set of pairs $s$ with $s_2$ supersingular and $s_1 = \varphi(s_2)$; a place specialisation $Psp$ of type `JHPlaceSpecialization p M H hpM A`, that is a map $\mathrm{sp}$ from places of $F'$ to places of $\bar F$ together with a homomorphism on degree-zero divisor classes, satisfying the structure's clauses (surjectivity of $\mathrm{sp}$, compatibility of push-forward of principal divisors with coefficientwise reduction of $q$-expansions, inertia-invariance, Frobenius-equivariance and divisor-class compatibility); and a prolongation datum $Rpd$ for $Psp$ and $\theta$, consisting of two regular prolongations $R_1, R_2$ of $A$ to $F_M$ with residues in $\bar F$, such that $R_1$ computes residues of elements coming from Laurent series over $A$ coefficientwise, and membership in and residues for $R_2$ are obtained from those for $R_1$ by applying $\theta$.
--
--   For a place $W$ of $F_M$ put $r_1(W) = \mathrm{sp}(W|_\alpha)$ (`reduceFst`) and $r_2(W) = \delta(\mathrm{sp}(W|_\beta))$ (`reduceSnd`), where $W|_\alpha$, $W|_\beta$ denote restriction along $\alpha$, $\beta$. A place $v$ of $\bar F$ is *fixed* (`Fixed`) when $\varphi(\delta(\varphi(v))) = v$, and *affine* (`IsAffinePlace`) when some element of $\bar F$ with $q$-expansion $j$ has a value at $v$. A place $W$ of $F_M$ is *strict of the first kind* (`IsStrictFst`) when $\delta(\varphi(r_1(W))) = r_2(W)$ and $r_1(W)$ is not fixed, and *strict of the second kind* (`IsStrictSnd`) when $r_1(W) = \varphi(r_2(W))$ and $r_2(W)$ is not fixed; `fstDiv` and `sndDiv` are the restrictions of a divisor to the places of the first, resp. second, kind. `IsInftySide` and `IsZeroSide` are the two cuspidal conditions of the project: cuspidality for $j$, resp. for $j(q^p)$, together with the requirement that $x'/x^p$, resp. $x/x'^p$, have a value at the place which is a unit residue $1$ of $A$, where $x$, $x'$ have $q$-expansions $j$ and $j(q^p)$.
--
--   The hypotheses on this data are: `hTD`, the type dichotomy, asserting that every place $W$ of $F_M$ satisfies $r_1(W) = \varphi(r_2(W))$ or $\delta(\varphi(r_1(W))) = r_2(W)$; `hFix`, finiteness of the set of fixed places of $\bar F$; `hmodel`, that $Rpd$ is a model, i.e. the two divisor laws (for bi-integral $f$ with nonzero residues, the $r_1$-push-forward of the first-kind part of the divisor of $f$ agrees with the order of the $R_1$-residue of $f$ at every non-fixed place, and likewise for $r_2$, the second-kind part and $R_2$) together with the two cusp laws (the analogous identities for the infinity-side part of the divisor at $r_1$ of an infinity-side place, and for the zero-side part at $r_2$ of a zero-side place); `hO`, the order law at fixed affine places, expressing the $r_1$-push-forward of the divisor of a bi-integral $f$ with nonzero residues at such a place $v$ as $\operatorname{ord}_v$ of the $R_1$-residue plus $\operatorname{ord}_{\delta(\varphi(v))}$ of the $R_2$-residue; `hRL`, the regularity law relative to $SS$ (two clauses: non-negativity of the two residue orders at fixed affine places where $f$ has no pole along $r_1$, and existence of a common value $c \in \kappa$ of the two residues at the two places of a pair in $SS$ under the same hypothesis); and `hNV`, the node value law, giving such a common value which is moreover nonzero, provided no place in the divisor of $f$ reduces to the pair.
--
--   The maps $\alpha$ and $\beta$ are prescribed on $q$-expansions: `hα_coe` says that $\alpha$ is the inclusion of $q$-expansions, and `hβ_coe` that $\beta$ is the substitution $q \mapsto q^p$ (`qExpand … p`); `hθgal` says that $\theta$ commutes with the arithmetic Galois action of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ on $F_M$; `hβθ` says that $\beta$ is $\alpha$ followed by $\theta$.
--
--   Two local hypotheses control residues of units near doubled poles. `hLFst`: for all places $Q \neq Q'$ of $F_M$, both strict of the first kind, with $r_1(Q') = r_1(Q)$ and $r_1(Q)$ affine, for every natural $n$ whose image in $\kappa$ is nonzero, every $g \in R_1$-integers with nonzero $R_1$-residue such that $\operatorname{ord}_Q g = -n$, $\operatorname{ord}_{Q'} g = n$ and $\operatorname{ord}_W g = 0$ for every further place $W$ of the first kind with $r_1(W) = r_1(Q)$, and for every $e \in A$ and $\varepsilon \in R_1$-integers with nonzero $R_1$-residue such that $g = 1 + e\varepsilon$, the order of the $R_1$-residue of $\varepsilon$ at $r_1(Q)$ is at least $-1$. `hLSnd` is the mirror statement with the second kind, $r_2$ and $R_2$.
--
--   `hUnit` asserts the existence of $u_1, u_2 \in F_M$ and divisors $D_1, D_2$ of $F_M$ with $D_1(W) = \operatorname{ord}_W u_1$ and $D_2(W) = \operatorname{ord}_W u_2$ for all $W$, such that: $u_1$ and $u_1^{-1}$ lie in the $R_1$-integers with nonzero $R_1$-residue, the $r_1$-push-forward of the first-kind part of $D_1$ agrees at every non-fixed place $v$ with $\operatorname{ord}_v$ of that residue, and the $r_1$-push-forward of the infinity-side part of $D_1$ agrees at $r_1(C)$ with $\operatorname{ord}_{r_1(C)}$ of that residue for every infinity-side place $C$; every nonzero $f \in F_M$ admits $m \neq 0$ and $j \in \mathbb{Z}$ with $f^m u_1^{\,j}$ in the $R_2$-integers with nonzero $R_2$-residue; symmetrically $u_2$ and $u_2^{-1}$ lie in the $R_2$-integers with nonzero $R_2$-residue, with the corresponding two identities for $r_2$, the second-kind part of $D_2$ and its zero-side part; and every nonzero $f$ admits $m \neq 0$ and $j \in \mathbb{Z}$ with $f^m u_2^{\,j}$ in the $R_1$-integers with nonzero $R_1$-residue. `hcusp` asserts that every non-affine place $w$ of $\bar F$ is $r_1(C)$ for some infinity-side place $C$ and $r_2(C')$ for some zero-side place $C'$.
--
--   Finally, $E$ is a divisor of $F_M$ with $E(V) \ge 0$ for all $V$ (`hE`), and $f \in F_M$ lies in the Riemann–Roch space of $E$ (so $\operatorname{ord}_V f \ge -E(V)$ for all $V$) and in the integers of both $R_1$ and $R_2$ (`h₁`, `h₂`).
--
--   The conclusion is a conjunction of three assertions.
--
--   First: for every divisor $D_1$ of $\bar F$ over $\kappa$ with $D_1(w) \ge 0$ for all $w$, such that the $r_1$-push-forward of the first-kind part of $E$ is $\le D_1$ at every non-fixed place, the $r_1$-push-forward of the part of $E$ supported away from the zero-side places is $\le D_1$ at every fixed non-affine place, and the $r_1$-push-forward of $E$ itself is $\le D_1$ at every fixed affine place, one has, for every place $w$ of $\bar F$: either the $R_1$-residue of $f$ is $0$, or $\operatorname{ord}_w$ of that residue is at least $-D_1(w)$.
--
--   Second: for every divisor $D_2$ of $\bar F$ with $D_2(w) \ge 0$ for all $w$, such that the $r_2$-push-forward of the second-kind part of $E$ is $\le D_2$ at every non-fixed place, the $r_2$-push-forward of the zero-side part of $E$ is $\le D_2(w)$ at every fixed place $w$ for which $\varphi(w)$ is not affine, and, at every fixed affine place $v$, the $r_1$-push-forward of $E$ at $v$ is $\le D_2(\delta(\varphi(v)))$, one has, for every place $w$ of $\bar F$: either the $R_2$-residue of $f$ is $0$, or $\operatorname{ord}_w$ of that residue is at least $-D_2(w)$.
--
--   Third: for every $s \in SS$ such that $\operatorname{ord}_V f \ge 0$ for every place $V$ of $F_M$ with $r_1(V) = s_1$, there exists $c \in \kappa$ such that the $R_1$-residue of $f$ has value $c$ at $s_1$ and the $R_2$-residue of $f$ has value $c$ at $s_2$. (No non-vanishing of $c$ is asserted here, in contrast with the node value law among the hypotheses.)
--
--   This is the basic bound on the pair of reductions of a function $f$ of $X_H(M)$ that is integral for both prolongations of the place $A$ at a prime $p$ exactly dividing the level: the two residues of a section of a non-negative divisor $E$ again lie in a Riemann–Roch space on the reduced curve, for any fibre divisor dominating the relevant push-forwards of $E$, and the two residues match at the supersingular node pairs. It is the primitive input to the constructions of common units with prescribed poles (of the first kind, of the second kind, and over a fixed place) and to the Riemann–Roch statement for reductions that cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHPlaceSpecialization_ProlongationDatum_residue_fst_box_and_residue_snd_box_and_node_hasValue_of_mem_riemannRochSpace.lean

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

theorem ModularCurve.JHPlaceSpecialization.ProlongationDatum.residue_fst_box_and_residue_snd_box_and_node_hasValue_of_mem_riemannRochSpace
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
    (E : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (hE : ∀ V, 0 ≤ E V)
    (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ riemannRochSpace E) (h₁ : f ∈ Rpd.R₁.integers) (h₂ : f ∈ Rpd.R₂.integers) :
    (∀ (D₁ : Divisor (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))), (∀ w, 0 ≤ D₁ w) →
      (∀ w, ¬ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ w → Finsupp.mapDomain (Psp.reduceFst α hα) (Psp.fstDiv α β hα hβ δ E) w ≤ D₁ w) →
      (∀ w, JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ w → ¬ JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A) w →
        Finsupp.mapDomain (Psp.reduceFst α hα) (E.filter (fun V => ¬ JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A) V)) w ≤ D₁ w) →
      (∀ v, JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v → JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A) v → Finsupp.mapDomain (Psp.reduceFst α hα) E v ≤ D₁ v) →
      ∀ w : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), Rpd.R₁.residue ⟨f, h₁⟩ = 0 ∨ -D₁ w ≤ w.ord (Rpd.R₁.residue ⟨f, h₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))) ∧
    (∀ (D₂ : Divisor (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))), (∀ w, 0 ≤ D₂ w) →
      (∀ w, ¬ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ w → Finsupp.mapDomain (Psp.reduceSnd β hβ δ) (Psp.sndDiv α β hα hβ δ E) w ≤ D₂ w) →
      (∀ w, JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ w → ¬ JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A) (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p w) →
        Finsupp.mapDomain (Psp.reduceSnd β hβ δ) (E.filter (fun V => JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A) V)) w ≤ D₂ w) →
      (∀ v, JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v → JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A) v → Finsupp.mapDomain (Psp.reduceFst α hα) E v ≤ D₂ (δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p v))) →
      ∀ w : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), Rpd.R₂.residue ⟨f, h₂⟩ = 0 ∨ -D₂ w ≤ w.ord (Rpd.R₂.residue ⟨f, h₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))) ∧
    (∀ s ∈ SS, (∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.reduceFst α hα V = s.1 → 0 ≤ V.ord f) →
      ∃ c : (ResidueField ↥A), s.1.HasValue (Rpd.R₁.residue ⟨f, h₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) c ∧ s.2.HasValue (Rpd.R₂.residue ⟨f, h₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) c) := by sorry
