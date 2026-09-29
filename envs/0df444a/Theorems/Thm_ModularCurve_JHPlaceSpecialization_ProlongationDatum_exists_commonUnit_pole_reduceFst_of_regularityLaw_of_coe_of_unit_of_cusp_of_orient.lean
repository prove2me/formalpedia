-- Prove2me | Theorems.Thm_ModularCurve_JHPlaceSpecialization_ProlongationDatum_exists_commonUnit_pole_reduceFst_of_regularityLaw_of_coe_of_unit_of_cusp_of_orient
-- name    : ModularCurve.JHPlaceSpecialization.ProlongationDatum.exists_commonUnit_pole_reduceFst_of_regularityLaw_of_coe_of_unit_of_cusp_of_orient
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/237aede7-9ef1-5495-9ce5-defe89cc33f7
-- title:
--   Common unit with a simple pole at V₀
-- statement:
--   Throughout, $p$ is a prime and $M$ a non-zero natural number with $p \mid M$ and $p^2 \nmid M$, and $H$ is a subgroup of $(\mathbb Z/M)^\times$; the hypothesis `hHp` requires that every unit of $\mathbb Z/M$ whose image under `ZMod.unitsMap` for $M/p \mid M$ is $1$ lies in $H$, and $M/p$ is non-zero. Further, $A$ is a valuation subring of $\overline{\mathbb Q}$ with $p$ a non-unit of $A$ (`A.LiesOverPrime p`), whose residue field $\kappa =$ `ResidueField ↥A` has characteristic $p$ and is algebraically closed. Write $F_M =$ `xHFunctionFieldBar M H` for the compositum of $\overline{\mathbb Q}$ with the $X_H$-function field inside Laurent series, $F_{M/p}$ for the same construction at level $M/p$ with the subgroup `infSubgroup p M H hpM` (the image of $H$ in $(\mathbb Z/(M/p))^\times$), and $\bar F =$ `JHNeronObjectAtP.Fbar p M H hpM κ`, the $q$-expansion function field over $\kappa$ for the group `JHNeronObjectAtP.ΓN p M H hpM`.
--
--   The remaining data are: an $\overline{\mathbb Q}$-algebra automorphism $\theta$ of $F_M$; two integral $\overline{\mathbb Q}$-algebra maps $\alpha,\beta : F_{M/p} \to F_M$ (integrality being `hα`, `hβ`); a unit $pb$ of $\mathbb Z/(M/p)$ with underlying element $p$ (`hpb`); a self-map $\delta$ of the set of places of $\bar F$ over $\kappa$, which by `hδ` is the semilinear action on places of the diamond automorphism `diamondActionModL` attached to a $\Gamma_0(M/p)$-lift [`CuspForm.gammaLift (M / p) pb`](def/CuspForm_HeckeOperatorFormsGammaH.html#L36) of $pb$; a finite set $SS$ of pairs of places of $\bar F$ which by `hSS` is exactly `ssNodePairsQExp κ (ΓN p M H hpM) p`, i.e. the set of pairs $s$ with $s_2$ supersingular and $s_1 = \varphi(s_2)$, where $\varphi =$ `qExpFrobeniusPlaceModL` denotes the Frobenius operation on places; a place specialisation datum $Psp$ of type `JHPlaceSpecialization p M H hpM A`, with underlying map $\mathrm{sp}$ from places of $F_{M/p}$ to places of $\bar F$; and a prolongation datum $Rpd$ for $Psp$ and $\theta$, consisting of two regular prolongations $R_1,R_2$ of $A$ from $F_M$ to $\bar F$ together with the $q$-expansion compatibility of $R_1$ and the identification of $R_2$ with the $\theta$-transport of $R_1$. Here `reduceFst` $= \mathrm{red}_1$ sends a place $W$ of $F_M$ to $\mathrm{sp}(W|_\alpha)$, and `reduceSnd` $=\mathrm{red}_2$ sends $W$ to $\delta(\mathrm{sp}(W|_\beta))$; $W$ is strict of the first kind when $\delta(\varphi(\mathrm{red}_1 W)) = \mathrm{red}_2 W$ and $\mathrm{red}_1 W$ is not fixed, and strict of the second kind when $\mathrm{red}_1 W = \varphi(\mathrm{red}_2 W)$ and $\mathrm{red}_2 W$ is not fixed, a place $v$ of $\bar F$ being fixed when $\varphi(\delta(\varphi(v))) = v$.
--
--   The structural hypotheses are grouped as follows. (i) Kit laws: `hTD` is the type dichotomy, that every place $W$ of $F_M$ satisfies $\mathrm{red}_1 W = \varphi(\mathrm{red}_2 W)$ or $\delta(\varphi(\mathrm{red}_1 W)) = \mathrm{red}_2 W$; `hFix` says the set of fixed places is finite; `hmodel` is `Rpd.IsModel`, the conjunction of the two divisor laws (for $f$ integral with non-zero residues for both prolongations, the $\mathrm{red}_1$-pushforward of the strict-first part of the divisor of $f$ agrees with the order of the $R_1$-residue of $f$ at every non-fixed place, and symmetrically for $\mathrm{red}_2$, the strict-second part and $R_2$) and the two cusp laws (the same comparison for the $\infty$-side part of the divisor under $\mathrm{red}_1$ at $\infty$-side places, and for the $0$-side part under $\mathrm{red}_2$ at $0$-side places); `hO` is the order law at fixed affine places, where the $\mathrm{red}_1$-pushforward of the full divisor equals the sum of the order of the $R_1$-residue at $v$ and of the order of the $R_2$-residue at $\delta(\varphi(v))$; `hRL` is the regularity law for $SS$ (non-negativity of the residue orders at fixed affine places, and existence of common values of the two residues at the two members of each node pair, under the corresponding non-negativity of $\mathrm{ord}_V f$); `hNV` is the node-value law for $SS$ (at a node pair missed by the divisor of $f$, the two residues take a common non-zero value at the two places of the pair). (ii) Normalisations: `hα_coe` says $\alpha$ is the identity on $q$-expansions, `hβ_coe` that $\beta$ acts by $q \mapsto q^p$, i.e. by `qExpand … p`, on $q$-expansions; `hθgal` says $\theta$ commutes with the arithmetic Galois semilinear action of $\overline{\mathbb Q} \simeq_{\mathbb Q} \overline{\mathbb Q}$ on $F_M$; and `hβθ` says $\beta = \theta \circ \alpha$.
--
--   (iii) The two disc laws. `hLFst` requires: for all places $Q \ne Q'$ of $F_M$, both strict of the first kind, with $\mathrm{red}_1 Q' = \mathrm{red}_1 Q$ and with $\mathrm{red}_1 Q$ an affine place (i.e. some $x \in \bar F$ with $q$-expansion `jqModC` has a value there), for every $n \in \mathbb N$ whose image in $\kappa$ is non-zero, every $g \in R_1$.integers with non-zero $R_1$-residue such that $\mathrm{ord}_Q g = -n$, $\mathrm{ord}_{Q'} g = n$ and $\mathrm{ord}_W g = 0$ for every further place $W$ strict of the first kind with $\mathrm{red}_1 W = \mathrm{red}_1 Q$ and $W \ne Q, Q'$, and for every $e \in A$ and $\varepsilon \in R_1$.integers with non-zero $R_1$-residue such that $g = 1 + e\varepsilon$, one has $-1 \le \mathrm{ord}_{\mathrm{red}_1 Q}$ of the $R_1$-residue of $\varepsilon$. `hLSnd` is the mirror statement with places strict of the second kind, $\mathrm{red}_2$ and $R_2$ throughout.
--
--   (iv) The modular-unit clause `hUnit` asserts the existence of $u_1, u_2 \in F_M$ and divisors $D_1, D_2$ of $F_M$ with $D_1 W = \mathrm{ord}_W u_1$ and $D_2 W = \mathrm{ord}_W u_2$ for all $W$, such that: $u_1$ lies in $R_1$.integers with non-zero residue and $u_1^{-1}$ also lies in $R_1$.integers, the $\mathrm{red}_1$-pushforward of the strict-first part of $D_1$ agrees at every non-fixed place $v$ with $\mathrm{ord}_v$ of the $R_1$-residue of $u_1$, and for every $\infty$-side place $C$ the $\mathrm{red}_1$-pushforward of the restriction of $D_1$ to the $\infty$-side places takes at $\mathrm{red}_1 C$ the value $\mathrm{ord}_{\mathrm{red}_1 C}$ of that residue; moreover every non-zero $f \in F_M$ admits $m \ne 0$ in $\mathbb N$ and $j \in \mathbb Z$ with $f^m u_1^j \in R_2$.integers of non-zero $R_2$-residue. Symmetrically $u_2$ is a unit for $R_2$ with non-zero residue, the $\mathrm{red}_2$-pushforward of the strict-second part of $D_2$ agrees at every non-fixed place with $\mathrm{ord}$ of the $R_2$-residue of $u_2$, the $\mathrm{red}_2$-pushforward of the $0$-side part of $D_2$ agrees at $\mathrm{red}_2 C$ for every $0$-side place $C$, and every non-zero $f$ admits $m \ne 0$ and $j$ with $f^m u_2^j \in R_1$.integers of non-zero $R_1$-residue. (v) The cusp-fibre clause `hcusp` requires every non-affine place $w$ of $\bar F$ to be of the form $\mathrm{red}_1 C$ for some $\infty$-side place $C$ and also $\mathrm{red}_2 C'$ for some $0$-side place $C'$. (vi) The orientation clauses: `horientInf` says $\delta(\varphi(\mathrm{red}_1 C)) = \mathrm{red}_2 C$ for every $\infty$-side place $C$, and `horient0` says $\mathrm{red}_1 C = \varphi(\mathrm{red}_2 C)$ for every $0$-side place $C$. Here being on the $\infty$-side means being cuspidal for the $j$-function together with the existence of $x, x'$ with $q$-expansions $j(q)$ and $j(q^p)$ and of $\tau \in A$ of residue $1$ at which the place takes the value $\tau$ on $x'/x^p$, and being on the $0$-side is the corresponding condition with $x/x'^p$ and cuspidality for $j(q^p)$.
--
--   Finally, $V_0$ is a place of $F_M$ which is either on the $\infty$-side or strict of the first kind (`hV₀`), $S$ is a finite set of elements of $\kappa$ and $B$ a finite set of places of $\bar F$.
--
--   Under these hypotheses there exist $g \in F_M$ and proofs that $g$ lies in $R_1$.integers and in $R_2$.integers, such that: the $R_1$-residue of $g$ is non-zero; the $R_2$-residue of $g$ is non-zero; $\mathrm{ord}_{V_0} g = -1$; for every place $V \ne V_0$ of $F_M$ with $\mathrm{ord}_V g < 0$, first, for every $xj \in F_M$ whose $q$-expansion is `jqModC` there is an $a \in A$ with $0 < \mathrm{ord}_V(xj - a)$ and with residue of $a$ in $\kappa$ outside $S$, second, $\mathrm{red}_1 V \notin B$, and third, $\mathrm{red}_2 V \notin B$; and $\mathrm{ord}_{\mathrm{red}_1 V_0}$ of the $R_1$-residue of $g$ equals $-1$.
--
--   This is the construction of a "common unit" on the two sheets of the $q$-expansion correspondence: a function on $X_H(M)$ integral with non-zero residue for both Gauss-type prolongations $R_1,R_2$ of the valuation subring $A$, having a simple pole at a prescribed place $V_0$ of the first sheet which survives as a simple pole of the first residue, and whose remaining poles avoid prescribed finite sets of $j$-residues and of fibre places. It is used in [`ModularCurve.JHPlaceSpecialization.exists_isPrincipal_apply_eq_neg_one_forall_support_good_of_isInftySide_or_isStrictFst`](thm.html#ModularCurve.JHPlaceSpecialization.exists_isPrincipal_apply_eq_neg_one_forall_support_good_of_isInftySide_or_isStrictFst), within the analysis of the mod-$p$ reduction of Jacobians of modular curves at level divisible by $p$ exactly once.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHPlaceSpecialization_ProlongationDatum_exists_commonUnit_pole_reduceFst_of_regularityLaw_of_coe_of_unit_of_cusp_of_orient.lean

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

theorem ModularCurve.JHPlaceSpecialization.ProlongationDatum.exists_commonUnit_pole_reduceFst_of_regularityLaw_of_coe_of_unit_of_cusp_of_orient
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
    (hV₀ : JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A) V₀ ∨ Psp.IsStrictFst α β hα hβ δ V₀)
    (S : Finset (ResidueField ↥A)) (B : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))) :
    ∃ (g : ↥(xHFunctionFieldBar M H)) (h₁ : g ∈ Rpd.R₁.integers) (h₂ : g ∈ Rpd.R₂.integers),
      Rpd.R₁.residue ⟨g, h₁⟩ ≠ 0 ∧ Rpd.R₂.residue ⟨g, h₂⟩ ≠ 0 ∧ V₀.ord g = -1 ∧
      (∀ V, V ≠ V₀ → V.ord g < 0 →
        (∀ (xj : ↥(xHFunctionFieldBar M H)), ((xj : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ) →
          ∃ a : ↥A, 0 < V.ord (xj - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a : AlgebraicClosure ℚ)) ∧ IsLocalRing.residue ↥A a ∉ S) ∧
          Psp.reduceFst α hα V ∉ B ∧ Psp.reduceSnd β hβ δ V ∉ B) ∧
      (Psp.reduceFst α hα V₀).ord (Rpd.R₁.residue ⟨g, h₁⟩) = -1 := by sorry
