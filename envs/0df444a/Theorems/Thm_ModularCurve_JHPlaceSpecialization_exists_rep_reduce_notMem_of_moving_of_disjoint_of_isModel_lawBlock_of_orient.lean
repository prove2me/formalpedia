-- Prove2me | Theorems.Thm_ModularCurve_JHPlaceSpecialization_exists_rep_reduce_notMem_of_moving_of_disjoint_of_isModel_lawBlock_of_orient
-- name    : ModularCurve.JHPlaceSpecialization.exists_rep_reduce_notMem_of_moving_of_disjoint_of_isModel_lawBlock_of_orient
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/2d47408e-2375-5ec7-adda-5163ba70e1c1
-- title:
--   Moving lemma for divisor classes on J_H(M) at p ∥ M
-- statement:
--   Fix a prime $p$ and a modulus $M$ with $p \mid M$ and $p^2 \nmid M$, and a subgroup $H \le (\mathbb{Z}/M)^{\times}$ such that every unit mapping to $1$ under the reduction $(\mathbb{Z}/M)^{\times} \to (\mathbb{Z}/(M/p))^{\times}$ lies in $H$ (hypothesis `hHp`). Write $F_M =$ `xHFunctionFieldBar M H` for the base change to $\overline{\mathbb{Q}}$ of the $q$-expansion function field of $X_H(M)$, $F_{M/p} =$ `xHFunctionFieldBar (M/p) (infSubgroup p M H hpM)` for the corresponding field at level $M/p$ with $H$ pushed forward along the reduction map, and $J_H(M) =$ `JH M H` for the group $\mathrm{Pic}^0$ of degree-zero divisor classes of $F_M$ over $\overline{\mathbb{Q}}$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ lying over $p$ (that is, $p$ is a non-unit of $A$), with residue field $\kappa$ of characteristic $p$ and algebraically closed, and write $\bar F =$ `JHNeronObjectAtP.Fbar p M H hpM κ` for the characteristic-$p$ $q$-expansion function field `qExpFunctionFieldC κ (JHNeronObjectAtP.ΓN p M H hpM)`, and $\mathrm{Fr} =$ `qExpFrobeniusPlaceModL κ (JHNeronObjectAtP.ΓN p M H hpM) p` for the $q$-expansion Frobenius on places of $\bar F$. Throughout, places are in the sense of [`AlgebraicCurve.Place`](def/AlgebraicCurve_DivisorClassGroup.html#L22) (valuation subrings containing the base field, proper, with principal maximal ideal), $v.\mathrm{ord}$ is the associated $\mathbb{Z}$-valued order function, and divisors are finitely supported $\mathbb{Z}$-valued functions on places.
--
--   The data are: an automorphism $\theta$ of $F_M$ over $\overline{\mathbb{Q}}$; two integral $\overline{\mathbb{Q}}$-algebra maps $\alpha, \beta : F_{M/p} \to F_M$ (integrality recorded by `hα`, `hβ`); a unit $pb$ of $\mathbb{Z}/(M/p)$ whose underlying residue is $p$ (hypothesis `hpb`); a self-map $\delta$ of the places of $\bar F$ which by `hδ` is the action of the semilinear automorphism attached to the diamond automorphism `diamondActionModL κ (M/p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M/p) pb)`; a finite set $SS$ of pairs of places of $\bar F$ which by `hSS` consists exactly of the node pairs `ssNodePairsQExp`, i.e. of the pairs $s$ with $s_2$ supersingular and $s_1 = \mathrm{Fr}(s_2)$; a place-specialisation package $\mathrm{Psp}$ of type `JHPlaceSpecialization p M H hpM A`, whose specialisation map $\mathrm{sp}$ sends places of $F_{M/p}$ to places of $\bar F$; and a prolongation datum $\mathrm{Rpd}$ for $\mathrm{Psp}$ and $\theta$, consisting of two regular prolongations $R_1, R_2$ of $A$ from $\overline{\mathbb{Q}}$ to $F_M$ with residue maps onto $\bar F$, linked by $\theta$. The two readings of a place $W$ of $F_M$ are $\mathrm{red}_1(W) = \mathrm{sp}(W|_{\alpha})$ and $\mathrm{red}_2(W) = \delta(\mathrm{sp}(W|_{\beta}))$, restriction being along $\alpha$, resp. $\beta$. A place $v$ of $\bar F$ is `Fixed` when $\mathrm{Fr}(\delta(\mathrm{Fr}\,v)) = v$; $W$ is strictly of the first type when $\delta(\mathrm{Fr}(\mathrm{red}_1 W)) = \mathrm{red}_2 W$ and $\mathrm{red}_1 W$ is not `Fixed`, and strictly of the second type when $\mathrm{red}_1 W = \mathrm{Fr}(\mathrm{red}_2 W)$ and $\mathrm{red}_2 W$ is not `Fixed`.
--
--   The law block consists of: the type dichotomy `hTD` (every place $W$ of $F_M$ satisfies $\mathrm{red}_1 W = \mathrm{Fr}(\mathrm{red}_2 W)$ or $\delta(\mathrm{Fr}(\mathrm{red}_1 W)) = \mathrm{red}_2 W$); the finiteness `hFix` of the set of `Fixed` places; `hmodel`, asserting that $\mathrm{Rpd}$ is a model for $\alpha, \beta, \delta$, i.e. the two divisor laws together with the two cusp laws at the $\infty$- and $0$-sides; `hO`, the order law at `Fixed` affine places (for $f$ integral with nonzero residues on both sides and $D$ the divisor of $f$, the $\mathrm{red}_1$-pushforward of $D$ at such a place $v$ is $v.\mathrm{ord}$ of the $R_1$-residue plus $(\delta(\mathrm{Fr}\,v)).\mathrm{ord}$ of the $R_2$-residue); `hRL`, the regularity law relative to $SS$ (two clauses, on non-negativity of the residue orders at `Fixed` affine places and on common values at the node pairs); and `hNV`, the node-value law relative to $SS$ (the two residues take a common nonzero value at the two coordinates of a node pair not met by the divisor of $f$).
--
--   The $q$-expansion readings are: `hα_coe`, that $\alpha$ is the identity on Laurent-series expansions; `hβ_coe`, that $\beta$ acts as the substitution $q \mapsto q^p$, i.e. `qExpand (AlgebraicClosure ℚ) p`, on expansions; `hθgal`, that $\theta$ commutes with the arithmetic Galois action of every $\sigma \in \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ on $F_M$; and `hβθ`, that $\beta$ is $\alpha$ followed by $\theta$.
--
--   The two local order bounds are symmetric. Hypothesis `hLFst` requires: for all places $Q \ne Q'$ of $F_M$, both strictly of the first type, with $\mathrm{red}_1(Q') = \mathrm{red}_1(Q)$ and this common place affine (in the sense of `IsAffinePlace`: it takes a value in $\kappa$ on an element of $\bar F$ whose expansion is `jqModC κ`), for every natural number $n$ with nonzero image in $\kappa$, every $g$ in the valuation ring of $R_1$ with nonzero $R_1$-residue satisfying $Q.\mathrm{ord}(g) = -n$, $Q'.\mathrm{ord}(g) = n$ and $W.\mathrm{ord}(g) = 0$ for every further strictly first-type $W$ with $\mathrm{red}_1(W) = \mathrm{red}_1(Q)$, and every $e \in A$ and $\varepsilon$ in the valuation ring of $R_1$ with nonzero $R_1$-residue such that $g = 1 + e\varepsilon$: the inequality $-1 \le (\mathrm{red}_1 Q).\mathrm{ord}$ of the $R_1$-residue of $\varepsilon$. Hypothesis `hLSnd` is the same statement with strict second type, $\mathrm{red}_2$ and $R_2$ throughout.
--
--   Hypothesis `hUnit` asserts the existence of $u_1, u_2 \in F_M$ and divisors $D_1, D_2$ which are the divisors of $u_1$, resp. $u_2$, such that: $u_1$ and $u_1^{-1}$ lie in the valuation ring of $R_1$, the $R_1$-residue of $u_1$ is nonzero, for every place $v$ of $\bar F$ which is not `Fixed` the $\mathrm{red}_1$-pushforward of the strict-first-type part $D_1.\mathrm{filter}$ at $v$ equals $v.\mathrm{ord}$ of that residue, and for every place $C$ of $F_M$ on the $\infty$-side the $\mathrm{red}_1$-pushforward of the restriction of $D_1$ to the $\infty$-side places, evaluated at $\mathrm{red}_1(C)$, equals $(\mathrm{red}_1 C).\mathrm{ord}$ of that residue; moreover every nonzero $f \in F_M$ admits $m \ne 0$ in $\mathbb{N}$ and $j \in \mathbb{Z}$ with $f^m u_1^{\,j}$ in the valuation ring of $R_2$ and of nonzero $R_2$-residue. The clauses for $u_2, D_2$ are the mirror ones, with $R_2$, $\mathrm{red}_2$, the strict-second-type part of $D_2$, the $0$-side places, and $f^m u_2^{\,j}$ required to be an $R_1$-integral element of nonzero $R_1$-residue. Here the $\infty$-side, resp. $0$-side, places are those satisfying `IsInftySide`, resp. `IsZeroSide`: cuspidality for $j$, resp. for its $p$-fold substitute, together with the existence of uniformisers $x, x'$ with expansions `jqModC` and its $q \mapsto q^p$ substitute and of $\tau \in A$ of residue $1$ at which the place takes the value $\tau$ on $x'/x^p$, resp. on $x/x'^p$.
--
--   Hypothesis `hcusp` asserts that every place $w$ of $\bar F$ which is not affine is simultaneously of the form $\mathrm{red}_1(C)$ for some $\infty$-side place $C$ of $F_M$ and of the form $\mathrm{red}_2(C)$ for some $0$-side place $C$. The orientation hypotheses are `horientInf`, that $\delta(\mathrm{Fr}(\mathrm{red}_1 C)) = \mathrm{red}_2(C)$ for every $\infty$-side place $C$, and `horient0`, that $\mathrm{red}_1(C) = \mathrm{Fr}(\mathrm{red}_2 C)$ for every $0$-side place $C$.
--
--   Under these hypotheses the following implication holds. Assume the moving input: for every finite set $T$ of places of $\bar F$ there exist divisors $E_0, C_0$ of $F_M$ such that $E_0$ is effective, $E_0$ is a good divisor (each place in its support is strictly of the first or of the second type), every $V$ in the support of $E_0$ satisfies $\mathrm{red}_1(V) \notin T$ and $\mathrm{red}_2(V) \notin T$, $\deg E_0 > 0$, $C_0$ is effective, $C_0$ is invariant under the arithmetic Galois action of every $\sigma$ in the inertia subgroup `A.inertiaSubgroupIn ℚ`, $\deg C_0 > 0$, and $E_0 - C_0$ is principal. Then for every finite set $T$ of places of $\bar F$ such that no $w \in T$ equals either coordinate of any pair $s \in SS$, and for every class $x \in J_H(M)$, there is a divisor $E$ of degree zero with $\mathrm{Pic}^0$-class $x$, that is `Pic0.mk E = x`, such that every $V$ in the support of $E$ satisfies $\mathrm{red}_1(V) \notin T$ and $\mathrm{red}_2(V) \notin T$.
--
--   This is the moving lemma for the level-$H$ specialisation kit of $X_H(M)$ at a prime $p$ exactly dividing $M$: it converts a supply of effective good divisors whose two readings avoid a prescribed finite set of places of the special fibre, together with an inertia-invariant effective divisor in the same class, into the statement that every class in $J_H(M)$ has a degree-zero representative both of whose readings avoid a prescribed finite set of non-nodal places. It is used in the construction of the reduction model of $J_H(M)$ at $p$, where representatives avoiding the nodal and the collision loci are needed to compute the specialisation of divisor classes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHPlaceSpecialization_exists_rep_reduce_notMem_of_moving_of_disjoint_of_isModel_lawBlock_of_orient.lean

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open scoped MatrixGroups

open Classical in

theorem ModularCurve.JHPlaceSpecialization.exists_rep_reduce_notMem_of_moving_of_disjoint_of_isModel_lawBlock_of_orient
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
    (Psp : JHPlaceSpecialization p M H hpM A)
    (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)
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
    (∀ T : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))),
      ∃ E₀ C₀ : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
        (∀ V, 0 ≤ E₀ V) ∧ Psp.IsGoodDiv α β hα hβ δ E₀ ∧
          (∀ V ∈ E₀.support, Psp.reduceFst α hα V ∉ T ∧ Psp.reduceSnd β hβ δ V ∉ T) ∧
            0 < Divisor.degree E₀ ∧ (∀ V, 0 ≤ C₀ V) ∧
              (∀ σ ∈ A.inertiaSubgroupIn ℚ, (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • C₀ = C₀) ∧
                0 < Divisor.degree C₀ ∧ Divisor.IsPrincipal (E₀ - C₀)) →
    ∀ (T : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))),
      (∀ w ∈ T, ∀ s ∈ SS, w ≠ s.1 ∧ w ≠ s.2) →
      ∀ x : JH M H,
        ∃ (E : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)))),
          Pic0.mk E = x ∧
            ∀ V ∈ (E : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)).support,
              Psp.reduceFst α hα V ∉ T ∧ Psp.reduceSnd β hβ δ V ∉ T := by sorry
