-- Prove2me | Theorems.Thm_ModularCurve_JHPlaceSpecialization_exists_addMonoidHom_isGluedSpecialization_of_isModel_of_coe_of_unit_of_cusp_of_orient
-- name    : ModularCurve.JHPlaceSpecialization.exists_addMonoidHom_isGluedSpecialization_of_isModel_of_coe_of_unit_of_cusp_of_orient
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/d6294c6a-3bef-5a0b-b8e7-a1b65fb1c91f
-- title:
--   Glued specialisation on the inertia invariants of J_H(M)
-- statement:
--   Fix natural numbers $p$ (prime) and $M \neq 0$ and a subgroup $H \le (\mathbb{Z}/M)^\times$, together with: a divisibility $p \mid M$ (`hpM`), the hypothesis `hpM2` that $p^2 \nmid M$, the hypothesis `hHp` that every $u \in (\mathbb{Z}/M)^\times$ with $\mathrm{unitsMap}(u) = 1$ in $(\mathbb{Z}/(M/p))^\times$ lies in $H$ (so $H$ contains the kernel of reduction from level $M$ to level $M/p$), and $M/p \neq 0$. Fix also a valuation subring $A$ of $\overline{\mathbb{Q}}$ with `hA : A.LiesOverPrime p`, i.e. $p$ is a non-unit of $A$, and assume its residue field $\kappa = \mathrm{ResidueField}\,A$ has characteristic $p$ and is algebraically closed. Write $F_M =$ `xHFunctionFieldBar M H` for the base change to $\overline{\mathbb{Q}}$ of the function field of $X_H(M)$ inside $\overline{\mathbb{Q}}$-Laurent series, $F_{M/p} =$ `xHFunctionFieldBar (M/p) (infSubgroup p M H hpM)` for the corresponding field at level $M/p$ with $H$ replaced by its image `infSubgroup p M H hpM` under $(\mathbb{Z}/M)^\times \to (\mathbb{Z}/(M/p))^\times$, and $\bar F =$ `JHNeronObjectAtP.Fbar p M H hpM κ`, the $q$-expansion function field `qExpFunctionFieldC κ (JHNeronObjectAtP.ΓN p M H hpM)` over $\kappa$. Throughout, $\varphi$ denotes the Frobenius operation `qExpFrobeniusPlaceModL κ (ΓN p M H hpM) p` on places of $\bar F$ over $\kappa$, obtained by restricting a place along the mod-$p$ Frobenius of $\bar F$.
--
--   The geometric data are: a $\overline{\mathbb{Q}}$-algebra automorphism $\theta$ of $F_M$; two $\overline{\mathbb{Q}}$-algebra maps $\alpha, \beta : F_{M/p} \to F_M$, integral by `hα`, `hβ`; a unit $pb$ of $\mathbb{Z}/(M/p)$ whose underlying residue is $p$ (`hpb`); and a self-map $\delta$ of the places of $\bar F$ over $\kappa$ which, by `hδ`, is the action on places of the semilinear automorphism attached to the diamond automorphism `diamondActionModL κ (M/p) (infSubgroup p M H hpM)` evaluated at a $\Gamma_0(M/p)$-lift of $pb$. A finite set $SS$ of pairs of places of $\bar F$ is given, and `hSS` states that $SS$ consists exactly of the pairs in `ssNodePairsQExp κ (ΓN p M H hpM) p`, that is the pairs $s$ with $s_2$ a supersingular place (`ssPlacesQExp`) and $s_1 = \varphi(s_2)$.
--
--   Further, $P_{sp}$ is a `JHPlaceSpecialization p M H hpM A`: a map $\mathrm{sp}$ from places of $F_{M/p}$ over $\overline{\mathbb{Q}}$ to places of $\bar F$ over $\kappa$ together with an additive map $\mathrm{spPic0} : \mathrm{Pic}^0(F_{M/p}) \to \mathrm{Pic}^0(\bar F)$, subject to the structure's axioms: compatibility of divisor pushforward with reduction of $q$-expansions (`d0_qexp`), surjectivity of $\mathrm{sp}$, the existence for each non-zero $f$ of a function on $\bar F$ whose divisor is the pushforward of the divisor of $f$ (`d5`), invariance of $\mathrm{sp}$ under the arithmetic Galois action by inertia at $A$ and its twisting by $\varphi$ under a Frobenius at $p$ (`d6_inertia`, `d6_frobenius`), and compatibility of $\mathrm{spPic0}$ with divisor pushforward (`spPic0_compat`). Finally $R_{pd}$ is a `ProlongationDatum` for $P_{sp}$ and $\theta$: two regular prolongations $R_1, R_2$ of $A$ from $\overline{\mathbb{Q}}$ to $F_M$ with residues in $\bar F$, a clause pinning the residue of $R_1$ on coefficientwise reductions of Laurent series over $A$, and the clauses $f \in R_2.\mathrm{integers} \iff \theta f \in R_1.\mathrm{integers}$ with $R_2$-residue of $f$ equal to the $R_1$-residue of $\theta f$.
--
--   For a place $W$ of $F_M$ put $r_1(W) = P_{sp}.\mathrm{reduceFst}\,\alpha\,W = \mathrm{sp}(W|_{\alpha})$ and $r_2(W) = P_{sp}.\mathrm{reduceSnd}\,\beta\,\delta\,W = \delta(\mathrm{sp}(W|_{\beta}))$, where $W|_\bullet$ is restriction along the indicated integral map; $W$ is of strict first type when $\delta(\varphi(r_1(W))) = r_2(W)$ and $r_1(W)$ is not $\delta$-fixed, and of strict second type when $r_1(W) = \varphi(r_2(W))$ and $r_2(W)$ is not $\delta$-fixed, where a place $v$ of $\bar F$ is $\delta$-fixed when $\varphi(\delta(\varphi(v))) = v$; $v$ is affine (`IsAffinePlace`) when there are $x$ in $\bar F$ with $q$-expansion `jqModC κ` and $a \in \kappa$ such that $v$ takes the value $a$ at $x$.
--
--   The law block consists of: `hTD`, the type dichotomy, asserting that every place $W$ of $F_M$ satisfies $r_1(W) = \varphi(r_2(W))$ or $\delta(\varphi(r_1(W))) = r_2(W)$; `hFix`, finiteness of the set of $\delta$-fixed places; `hmodel`, the conjunction `Rpd.IsModel` of the divisor laws `DivisorLawFst`, `DivisorLawSnd` and the cusp laws `CuspLawInfty`, `CuspLawZero` for $(\alpha,\beta,\delta)$; `hO`, the order law at fixed places, requiring for every $f$ lying in the integers of both $R_1$ and $R_2$ with both residues non-zero, every divisor $D$ of $f$ and every $\delta$-fixed affine place $v$, that the pushforward $r_{1*}D$ at $v$ equal $v.\mathrm{ord}$ of the $R_1$-residue of $f$ plus $(\delta(\varphi(v))).\mathrm{ord}$ of the $R_2$-residue of $f$; `hRL`, the regularity law for $SS$, whose two clauses assert for $f$ in both rings of integers that non-negativity of $\mathrm{ord}_V f$ along all $V$ reducing to a $\delta$-fixed affine place $v$ forces non-negativity of the orders of the two residues at $v$ and at $\delta(\varphi(v))$, and that non-negativity along all $V$ with $r_1(V) = s_1$ yields a common value $c \in \kappa$ of the $R_1$-residue at $s_1$ and the $R_2$-residue at $s_2$ for each $s \in SS$; and `hNV`, the node-value law, requiring that for such $f$ and $s \in SS$, if no place $V$ with $\mathrm{ord}_V f \neq 0$ satisfies $r_1(V) = s_1$ and $r_2(V) = s_2$, then the two residues take a common non-zero value at $s_1$ and $s_2$.
--
--   The $q$-expansion and transport hypotheses are: `hα_coe`, that $\alpha$ preserves Laurent series, i.e. the $q$-expansion of $\alpha u$ equals that of $u$; `hβ_coe`, that the $q$-expansion of $\beta u$ is obtained from that of $u$ by the substitution `qExpand ... p` multiplying exponents by $p$; `hθgal`, that $\theta$ commutes with the arithmetic Galois action of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ on $F_M$; and `hβθ`, that $\beta$ is $\alpha$ followed by $\theta$.
--
--   Two symmetric hypotheses `hLFst` and `hLSnd` (the disc laws) are imposed. `hLFst` states: for places $Q \neq Q'$ of $F_M$ of strict first type with $r_1(Q') = r_1(Q)$ and $r_1(Q)$ affine, for every natural $n$ whose image in $\kappa$ is non-zero, every $g$ in the integers of $R_1$ with non-zero $R_1$-residue such that $\mathrm{ord}_Q g = -n$, $\mathrm{ord}_{Q'} g = n$ and $\mathrm{ord}_W g = 0$ for every other strict-first place $W$ with $r_1(W) = r_1(Q)$, and for every $e \in A$ and $\varepsilon$ in the integers of $R_1$ with non-zero residue such that $g = 1 + e\,\varepsilon$ (the image of $e$ in $F_M$ being taken), one has $-1 \le (r_1(Q)).\mathrm{ord}$ of the $R_1$-residue of $\varepsilon$. The hypothesis `hLSnd` is the same statement with strict second type, $r_2$ and $R_2$ in place of strict first type, $r_1$ and $R_1$.
--
--   The hypothesis `hUnit` (the modular-unit clause) requires the existence of $u_1, u_2 \in F_M$ and divisors $D_1, D_2$ on $F_M$ with $D_1 W = \mathrm{ord}_W u_1$ and $D_2 W = \mathrm{ord}_W u_2$ for all $W$, such that: $u_1$ and $u_1^{-1}$ lie in the integers of $R_1$, the $R_1$-residue of $u_1$ is non-zero, the pushforward under $r_1$ of the restriction of $D_1$ to strict-first places takes, at every place $v$ of $\bar F$ that is not $\delta$-fixed, the value $v.\mathrm{ord}$ of that residue, and the pushforward under $r_1$ of the restriction of $D_1$ to $\infty$-side places takes at $r_1(C)$, for every $\infty$-side place $C$, the value $(r_1(C)).\mathrm{ord}$ of that residue; every non-zero $f \in F_M$ admits $m \neq 0$ in $\mathbb{N}$ and $j \in \mathbb{Z}$ with $f^m u_1^{\,j}$ in the integers of $R_2$ and with non-zero $R_2$-residue; and the mirror-image four conditions for $u_2$, with $R_2$, $r_2$, the restriction of $D_2$ to strict-second places, the $0$-side places, and for every non-zero $f$ some $m \neq 0$, $j$ with $f^m u_2^{\,j}$ in the integers of $R_1$ with non-zero $R_1$-residue. Here a place $C$ of $F_M$ is $\infty$-side (`IsInftySide`) when it is `IsCuspidal` and there are $x, x'$ in $F_M$ with $q$-expansions `jqModC` and its $p$-fold substitution, and $\tau \in A$ with residue $1$, such that $C$ takes the value $\tau$ at $x'/x^p$; it is $0$-side (`IsZeroSide`) when it is `IsCuspidal'` and, with the same $x, x'$ and $\tau$, takes the value $\tau$ at $x/x'^p$.
--
--   The cusp clause `hcusp` states that every place $w$ of $\bar F$ which is not affine is $r_1(C)$ for some $\infty$-side place $C$ and $r_2(C')$ for some $0$-side place $C'$. The two orientation clauses are `horientInf`, that $\delta(\varphi(r_1(C))) = r_2(C)$ for every $\infty$-side place $C$, and `horient0`, that $r_1(C) = \varphi(r_2(C))$ for every $0$-side place $C$.
--
--   Under all of these hypotheses the conclusion asserts the existence of an additive group homomorphism
--   $$\mathrm{sp}_J : \ \mathrm{inertiaInvariants}\,M\,H\,A \longrightarrow \mathrm{GluedPic}^0(\kappa, \bar F, SS),$$
--   from the subgroup of `JH M H` consisting of the elements fixed by every $\sigma$ in the inertia subgroup `A.inertiaSubgroupIn ℚ` to the quotient of the group of admissible gluing data (pairs of degree-zero divisors on $\bar F$ together with a family of elements of $\kappa^\times$ indexed by $SS$, the two divisors vanishing at the first, respectively second, component of each pair in $SS$) by the subgroup of glued principal data, which is a glued specialisation in the sense of `Psp.IsGluedSpecialization α β hα hβ δ SS`: for every degree-zero divisor $D$ on $F_M$ whose class $\mathrm{Pic}^0.\mathrm{mk}\,D$ lies in `inertiaInvariants M H A`, and every admissible gluing datum $x$, if every place in the support of $D$ is of strict first or strict second type and $x$ equals the gluing datum `Psp.glueData α β hα hβ δ SS D` attached to $D$, then $\mathrm{sp}_J$ sends the class of $D$ to the class of $x$ in $\mathrm{GluedPic}^0(\kappa,\bar F, SS)$.
--
--   This is the specialisation map for the Picard group of the semistable fibre of $J_H(M)$ at a prime $p$ exactly dividing the level: it realises the inertia invariants of $J_H(M)(\overline{\mathbb{Q}})$ inside the glued degree-zero Picard group of the mod-$p$ fibre, whose gluing is along the supersingular node pairs $SS$. It is the existence step used by [`ModularCurve.JHPlaceSpecialization.exists_componentMap_gluedSpecialization_of_isModel_of_coe_of_unit_of_cusp_of_attachedAnnulus_of_slope_of_fixReg`](thm.html#ModularCurve.JHPlaceSpecialization.exists_componentMap_gluedSpecialization_of_isModel_of_coe_of_unit_of_cusp_of_attachedAnnulus_of_slope_of_fixReg), which combines it with the component-group description in the level-lowering argument at $p \,\|\, M$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHPlaceSpecialization_exists_addMonoidHom_isGluedSpecialization_of_isModel_of_coe_of_unit_of_cusp_of_orient.lean

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_AlgebraicCurve_SemistableCharts

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open scoped MatrixGroups

open Classical in

theorem ModularCurve.JHPlaceSpecialization.exists_addMonoidHom_isGluedSpecialization_of_isModel_of_coe_of_unit_of_cusp_of_orient
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
      Psp.reduceFst α hα C = qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (Psp.reduceSnd β hβ δ C)) :
    ∃ spJ : ↥(JHPlaceSpecialization.inertiaInvariants M H A) →+ GluedPic0 (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) SS,
      Psp.IsGluedSpecialization α β hα hβ δ SS spJ := by sorry
