-- Prove2me | Theorems.Thm_ModularCurve_JHPlaceSpecialization_ProlongationDatum_exists_commonUnit_pole_of_reduceFst_fixed_of_isAffinePlace_of_regularityLaw_of_coe_of_unit_of_cusp_of_orient
-- name    : ModularCurve.JHPlaceSpecialization.ProlongationDatum.exists_commonUnit_pole_of_reduceFst_fixed_of_isAffinePlace_of_regularityLaw_of_coe_of_unit_of_cusp_of_orient
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/3300a5ec-cce8-5bf0-8894-d5956461e5e6
-- title:
--   Common unit with a simple pole at a fixed place
-- statement:
--   Throughout, $p$ is a prime and $M \neq 0$ a natural number with $p \mid M$ and $p^{2} \nmid M$, and $H \le (\mathbb{Z}/M)^{\times}$ is a subgroup containing every unit $u$ with $\mathrm{unitsMap}\,u = 1$ under the reduction $(\mathbb{Z}/M)^{\times} \to (\mathbb{Z}/(M/p))^{\times}$ (hypothesis `hHp`), with $M/p \neq 0$. Further, $A$ is a valuation subring of $\overline{\mathbb{Q}}$ lying over $p$, in the sense that $p$ is a non-unit of $A$ (`hA`), and its residue field $\kappa := \mathrm{ResidueField}\,A$ is of characteristic $p$ and algebraically closed. Write $F_M := \,$`xHFunctionFieldBar M H` and $F_{M/p} := \,$`xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)` for the base changes to $\overline{\mathbb{Q}}$ of the $q$-expansion function fields of $X_H(M)$ and of $X_{H'}(M/p)$, where `infSubgroup p M H hpM` is the image of $H$ in $(\mathbb{Z}/(M/p))^{\times}$; write $\bar F := \,$`JHNeronObjectAtP.Fbar p M H hpM κ`, the $q$-expansion function field over $\kappa$ for $\Gamma' := \,$`JHNeronObjectAtP.ΓN p M H hpM`, and $\varphi := \,$`qExpFrobeniusPlaceModL κ Γ′ p` for the Frobenius operator on places of $\bar F$ over $\kappa$.
--
--   The data are: a $\overline{\mathbb{Q}}$-algebra automorphism $\theta$ of $F_M$; two integral $\overline{\mathbb{Q}}$-algebra maps $\alpha, \beta : F_{M/p} \to F_M$ (integrality being `hα`, `hβ`); a unit $pb$ of $\mathbb{Z}/(M/p)$ whose underlying residue is $p$ (`hpb`); a self-map $\delta$ of the set of places of $\bar F$ over $\kappa$, which by `hδ` is the action $v \mapsto \mathrm{SemilinearAut.ofAlgAut}(\mathrm{diamondActionModL}\,\kappa\,(M/p)\,H'\,(\mathrm{CuspForm.gammaLift}\,(M/p)\,pb)) \cdot v$ of the diamond operator attached to $pb$ at level $M/p$; a finite set $SS$ of pairs of places of $\bar F$ which by `hSS` consists exactly of the pairs $(\varphi w, w)$ with $w$ supersingular, i.e. the members of `ssNodePairsQExp κ Γ′ p`; a place specialisation $Psp : \,$`JHPlaceSpecialization p M H hpM A`, whose underlying map $\mathrm{sp}$ sends places of $F_{M/p}$ over $\overline{\mathbb{Q}}$ to places of $\bar F$ over $\kappa$; and a prolongation datum $Rpd$ for $Psp$ and $\theta$, consisting of two regular prolongations $R_1, R_2$ of $A$ from $F_M$ to $\bar F$ with $R_2$-integers the $\theta$-preimage of the $R_1$-integers and $R_2$-residue equal to the $R_1$-residue of $\theta$. Throughout, $\mathrm{red}_1 W := \mathrm{sp}(W|_{\alpha})$ and $\mathrm{red}_2 W := \delta(\mathrm{sp}(W|_{\beta}))$ denote the two readings of a place $W$ of $F_M$ (restriction along $\alpha$, resp. $\beta$, followed by $\mathrm{sp}$, resp. by $\mathrm{sp}$ and $\delta$); a place $v$ of $\bar F$ is *fixed* when $\varphi(\delta(\varphi v)) = v$, and *affine* when some $x \in \bar F$ with $q$-expansion `jqModC κ` has a value at $v$.
--
--   The hypotheses fall into the following groups.
--
--   Laws of the specialisation: `hTD` (type dichotomy) asserts that every place $W$ of $F_M$ satisfies $\mathrm{red}_1 W = \varphi(\mathrm{red}_2 W)$ or $\delta(\varphi(\mathrm{red}_1 W)) = \mathrm{red}_2 W$; `hFix` asserts that the set of fixed places of $\bar F$ is finite; `hmodel` is the conjunction of the two divisor laws and the two cusp laws (for a function $f$ whose two residues are non-zero, the divisor of $f$ pushed forward along $\mathrm{red}_1$ from its strict-first part computes the order of the $R_1$-residue of $f$ at each non-fixed place, and symmetrically for $\mathrm{red}_2$, $R_2$ and the strict-second part; the cusp laws are the corresponding identities for the $\infty$-side, resp. zero-side, parts of the divisor at the readings of $\infty$-side, resp. zero-side, places); `hO` is the order law at fixed affine places (there the pushforward of the whole divisor equals the sum of the order of the $R_1$-residue at $v$ and the order of the $R_2$-residue at $\delta(\varphi v)$); `hRL` is the two-clause regularity law relative to $SS$; `hNV` is the node-value law relative to $SS$ (a common value of the two residues at the two components of a node pair).
--
--   Pinning of the two sheets: `hα_coe` states that $\alpha$ is the identity on $q$-expansions, `hβ_coe` that $\beta$ is substitution $q \mapsto q^{p}$, that is `qExpand (AlgebraicClosure ℚ) p` on $q$-expansions; `hθgal` states that $\theta$ commutes with the arithmetic Galois action of $\mathrm{Aut}(\overline{\mathbb{Q}}/\mathbb{Q})$ on $F_M$; `hβθ` states $\beta = \theta \circ \alpha$.
--
--   Two pole-bound laws: `hLFst` concerns places $Q \neq Q'$ of $F_M$ that are strict-first (that is, $\delta(\varphi(\mathrm{red}_1\,\cdot)) = \mathrm{red}_2\,\cdot$ and $\mathrm{red}_1\,\cdot$ is not fixed) with the same, affine, first reading, a natural number $n$ non-zero in $\kappa$, and $g$ in the $R_1$-integers with non-zero residue such that $\mathrm{ord}_Q g = -n$, $\mathrm{ord}_{Q'} g = n$ and $\mathrm{ord}_W g = 0$ for every further strict-first $W$ with the same first reading; if moreover $g = 1 + e\varepsilon$ with $e \in A$ and $\varepsilon$ in the $R_1$-integers with non-zero residue, then the order of the $R_1$-residue of $\varepsilon$ at $\mathrm{red}_1 Q$ is at least $-1$. The hypothesis `hLSnd` is the same statement with strict-second places, $\mathrm{red}_2$ and $R_2$ throughout.
--
--   A modular-unit clause `hUnit`: there exist $u_1, u_2 \in F_M$ and divisors $D_1, D_2$ with $D_1 W = \mathrm{ord}_W u_1$ and $D_2 W = \mathrm{ord}_W u_2$ for all $W$, such that $u_1$ and $u_1^{-1}$ lie in the $R_1$-integers with $R_1$-residue of $u_1$ non-zero, the divisor law along $\mathrm{red}_1$ holds for the strict-first part of $D_1$ at every non-fixed place and the $\infty$-side cusp law holds for $D_1$; every non-zero $f \in F_M$ admits $m \neq 0$ and $j \in \mathbb{Z}$ with $f^{m}u_1^{j}$ in the $R_2$-integers with non-zero $R_2$-residue; symmetrically $u_2$ and $u_2^{-1}$ lie in the $R_2$-integers with $R_2$-residue of $u_2$ non-zero, the divisor law along $\mathrm{red}_2$ holds for the strict-second part of $D_2$ at every non-fixed place and the zero-side cusp law holds for $D_2$; and every non-zero $f \in F_M$ admits $m \neq 0$ and $j \in \mathbb{Z}$ with $f^{m}u_2^{j}$ in the $R_1$-integers with non-zero $R_1$-residue.
--
--   A cusp-fibre clause `hcusp`: every non-affine place $w$ of $\bar F$ is the first reading of some $\infty$-side place and the second reading of some zero-side place. Two orientation clauses: `horientInf` states $\delta(\varphi(\mathrm{red}_1 C)) = \mathrm{red}_2 C$ for every $\infty$-side place $C$, and `horient0` states $\mathrm{red}_1 C = \varphi(\mathrm{red}_2 C)$ for every zero-side place $C$. Here a place $C$ is $\infty$-side when it is cuspidal (for $x$ with $q$-expansion `jqModC` and every $a \in A$, $\mathrm{ord}_C(x - a) \le 0$) and $x'/x^{p}$ has a value at $C$ with residue $1$, where $x, x'$ have $q$-expansions $j(q)$ and $j(q^{p})$; zero-side is the mirror condition with $x/x'^{p}$ and the cuspidality condition stated for $j(q^{p})$.
--
--   Finally, $V_0$ is a place of $F_M$ whose first reading $\mathrm{red}_1 V_0$ is fixed (`hfix`), is affine (`haff`), and is neither component of any pair in $SS$ (`hord`); and $S$ is a finite set of elements of $\kappa$, $B$ a finite set of places of $\bar F$.
--
--   Under these hypotheses there exists $g \in F_M$ lying both in the $R_1$-integers and in the $R_2$-integers such that: the $R_1$-residue of $g$ is non-zero; the $R_2$-residue of $g$ is non-zero; $\mathrm{ord}_{V_0} g = -1$; for every place $V \neq V_0$ of $F_M$ with $\mathrm{ord}_V g < 0$ one has, firstly, that for every $x_j \in F_M$ whose $q$-expansion is `jqModC (AlgebraicClosure ℚ)` there is $a \in A$ with $0 < \mathrm{ord}_V(x_j - a)$ and residue of $a$ outside $S$, and secondly that $\mathrm{red}_1 V \notin B$ and $\mathrm{red}_2 V \notin B$; and lastly the pair of orders of the two residues of $g$ at the two places attached to $V_0$ takes one of two values: either the order of the $R_1$-residue of $g$ at $\mathrm{red}_1 V_0$ is $-1$ and the order of the $R_2$-residue of $g$ at $\delta(\varphi(\mathrm{red}_1 V_0))$ is $0$, or the former order is $0$ and the latter is $-1$.
--
--   This is the existence statement, on the two-sheeted reduction of $X_H(M)$ at $p$ encoded by a place specialisation together with a prolongation datum, of a function that is a unit for both regular prolongations, has a simple pole at a prescribed place $V_0$ whose first reading is a fixed affine place, has all remaining poles avoiding two prescribed finite sets of data, and distributes that single pole over exactly one of the two sheets. It is used by [`ModularCurve.JHPlaceSpecialization.exists_isPrincipal_apply_eq_neg_one_forall_support_good_of_fixed_of_isAffinePlace`](thm.html#ModularCurve.JHPlaceSpecialization.exists_isPrincipal_apply_eq_neg_one_forall_support_good_of_fixed_of_isAffinePlace) in the analysis of the specialisation of divisor classes at a prime exactly dividing the level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHPlaceSpecialization_ProlongationDatum_exists_commonUnit_pole_of_reduceFst_fixed_of_isAffinePlace_of_regularityLaw_of_coe_of_unit_of_cusp_of_orient.lean

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

theorem ModularCurve.JHPlaceSpecialization.ProlongationDatum.exists_commonUnit_pole_of_reduceFst_fixed_of_isAffinePlace_of_regularityLaw_of_coe_of_unit_of_cusp_of_orient
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
    (hfix : JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ (Psp.reduceFst α hα V₀))
    (haff : JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A) (Psp.reduceFst α hα V₀))
    (hord : ∀ s ∈ SS, Psp.reduceFst α hα V₀ ≠ s.1 ∧ Psp.reduceFst α hα V₀ ≠ s.2)
    (S : Finset (ResidueField ↥A)) (B : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))) :
    ∃ (g : ↥(xHFunctionFieldBar M H)) (h₁ : g ∈ Rpd.R₁.integers) (h₂ : g ∈ Rpd.R₂.integers),
      Rpd.R₁.residue ⟨g, h₁⟩ ≠ 0 ∧ Rpd.R₂.residue ⟨g, h₂⟩ ≠ 0 ∧ V₀.ord g = -1 ∧
      (∀ V, V ≠ V₀ → V.ord g < 0 →
        (∀ (xj : ↥(xHFunctionFieldBar M H)), ((xj : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ) →
          ∃ a : ↥A, 0 < V.ord (xj - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a : AlgebraicClosure ℚ)) ∧ IsLocalRing.residue ↥A a ∉ S) ∧
          Psp.reduceFst α hα V ∉ B ∧ Psp.reduceSnd β hβ δ V ∉ B) ∧
      (((Psp.reduceFst α hα V₀).ord (Rpd.R₁.residue ⟨g, h₁⟩) = -1 ∧
          (δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (Psp.reduceFst α hα V₀))).ord (Rpd.R₂.residue ⟨g, h₂⟩) = 0) ∨
        ((Psp.reduceFst α hα V₀).ord (Rpd.R₁.residue ⟨g, h₁⟩) = 0 ∧
          (δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (Psp.reduceFst α hα V₀))).ord (Rpd.R₂.residue ⟨g, h₂⟩) = -1)) := by sorry
