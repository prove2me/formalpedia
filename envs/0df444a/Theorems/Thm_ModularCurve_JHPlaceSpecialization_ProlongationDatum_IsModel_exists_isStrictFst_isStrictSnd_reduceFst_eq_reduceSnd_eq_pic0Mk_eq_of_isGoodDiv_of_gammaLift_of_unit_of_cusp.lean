-- Prove2me | Theorems.Thm_ModularCurve_JHPlaceSpecialization_ProlongationDatum_IsModel_exists_isStrictFst_isStrictSnd_reduceFst_eq_reduceSnd_eq_pic0Mk_eq_of_isGoodDiv_of_gammaLift_of_unit_of_cusp
-- name    : ModularCurve.JHPlaceSpecialization.ProlongationDatum.IsModel.exists_isStrictFst_isStrictSnd_reduceFst_eq_reduceSnd_eq_pic0Mk_eq_of_isGoodDiv_of_gammaLift_of_unit_of_cusp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/bda5bee1-2f4f-5ecd-b2fb-5d05206860da
-- title:
--   Two-sided representative of a glued-trivial divisor class on X_H(M)
-- statement:
--   Throughout, places, divisors and divisor classes are those of the project: a place of a field extension $F/K$ is a proper valuation subring of $F$ containing the image of $K$ whose ideals are principal, `ord` is the associated normalised integer valuation, a divisor is a finitely supported $\mathbb{Z}$-valued function on places, `Divisor.degZero` is the kernel of the degree map, `Pic0` is the quotient of the degree-zero divisors by the principal ones, and for a finite set $SS$ of pairs of places `GluedPic0` is the quotient of the admissible gluing data (pairs of degree-zero divisors vanishing at the two coordinates of every pair of $SS$, together with a family of constants) by the glued-principal ones.
--
--   Arithmetic data. Fixed are a prime $p$ and a positive integer $M$ with $p \mid M$ (`hpM`) and $p^{2} \nmid M$ (`hpM2`), a subgroup $H \le (\mathbb{Z}/M)^{\times}$ such that every unit $u$ whose image under reduction $(\mathbb{Z}/M)^{\times} \to (\mathbb{Z}/(M/p))^{\times}$ is $1$ lies in $H$ (`hHp`), with $M/p$ nonzero, and a valuation subring $A$ of an algebraic closure of $\mathbb{Q}$ with $p$ a non-unit of $A$ (`hA`), whose residue field $\kappa =$ `ResidueField ↥A` has characteristic $p$ and is algebraically closed. Write $F =$ `↥(xHFunctionFieldBar M H)` for the base change to $\overline{\mathbb{Q}}$ of the function field of $X_H(M)$ realised inside Laurent series, $F' =$ `↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))` for the corresponding field at level $M/p$ with the group `infSubgroup p M H hpM` the image of $H$ under reduction, and $\bar F =$ `JHNeronObjectAtP.Fbar p M H hpM κ`, the $q$-expansion function field over $\kappa$ attached to `JHNeronObjectAtP.ΓN p M H hpM`.
--
--   Degeneracy data. Given are a $\overline{\mathbb{Q}}$-algebra automorphism $\theta$ of $F$, two $\overline{\mathbb{Q}}$-algebra maps $\alpha, \beta : F' \to F$ with `α.IsIntegral` and `β.IsIntegral` (`hα`, `hβ`), a unit $pb$ of $\mathbb{Z}/(M/p)$ whose underlying element is $p$ (`hpb`), and a map $\delta$ on the places of $\bar F$ over $\kappa$ which, by `hδ`, is the action through `SemilinearAut.ofAlgAut` of the diamond automorphism `diamondActionModL κ (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)`. A finite set $SS$ of pairs of places of $\bar F$ is prescribed by `hSS` to consist exactly of the node pairs `ssNodePairsQExp κ (JHNeronObjectAtP.ΓN p M H hpM) p`, that is, the pairs $s$ whose second coordinate is a supersingular place and whose first coordinate is the `qExpFrobeniusPlaceModL`-image of the second.
--
--   Specialisation and prolongations. $Psp$ is a `JHPlaceSpecialization p M H hpM A`: a map `sp` from the places of $F'$ over $\overline{\mathbb{Q}}$ to the places of $\bar F$ over $\kappa$ together with a homomorphism `spPic0` on degree-zero classes, subject to the structure's compatibility with coefficientwise reduction of $q$-expansions, surjectivity of `sp`, existence of reductions of principal divisors, invariance under inertia, the Frobenius rule for Frobenius elements at $p$, and compatibility of `spPic0` with pushforward of divisors. $Rpd$ is a `ProlongationDatum Psp θ`: two regular prolongations $R_1, R_2$ of $A$ to $F$ with residues in $\bar F$, the first computing coefficientwise reduction of Laurent series with coefficients in $A$, the second the $\theta$-conjugate of the first ($f \in R_2$.`integers` iff $\theta f \in R_1$.`integers`, and $R_2$.`residue` $f = R_1$.`residue` $(\theta f)$). For a place $Q$ of $F$ one writes `reduceFst` $Q =$ `sp` of the restriction of $Q$ along $\alpha$, and `reduceSnd` $Q = \delta($`sp` of the restriction of $Q$ along $\beta)$; $Q$ is strict of the first kind (`IsStrictFst`) when $\delta(\mathrm{Frob}(\mathrm{red}_1 Q)) = \mathrm{red}_2 Q$ and $\mathrm{red}_1 Q$ is not $\delta$-Frobenius fixed, and strict of the second kind (`IsStrictSnd`) when $\mathrm{red}_1 Q = \mathrm{Frob}(\mathrm{red}_2 Q)$ and $\mathrm{red}_2 Q$ is not $\delta$-Frobenius fixed, where $\mathrm{Frob} =$ `qExpFrobeniusPlaceModL κ _ p` and a place $v$ of $\bar F$ is fixed (`Fixed`) when $\mathrm{Frob}(\delta(\mathrm{Frob}\, v)) = v$; $v$ is affine (`IsAffinePlace`) when some element of $\bar F$ with $q$-expansion `jqModC κ` takes a value in $\kappa$ at $v$.
--
--   Laws. `hTD` is the type dichotomy: every place $W$ of $F$ satisfies $\mathrm{red}_1 W = \mathrm{Frob}(\mathrm{red}_2 W)$ or $\delta(\mathrm{Frob}(\mathrm{red}_1 W)) = \mathrm{red}_2 W$. `hmodel` is `IsModel`, the conjunction of the four laws `DivisorLawFst`, `DivisorLawSnd`, `CuspLawInfty` and `CuspLawZero` for $Rpd$ relative to $\alpha, \beta, \delta$, governing the two one-sided divisor computations and the behaviour at the two families of cusps. `hO` is `OrderLawFixed`: for $f \in F$ lying in both $R_1$.`integers` and $R_2$.`integers` with both residues nonzero, and $D$ the divisor of $f$, every fixed affine place $v$ of $\bar F$ satisfies $(\mathrm{red}_1)_{*}D(v) = \mathrm{ord}_v(R_1\text{-residue of } f) + \mathrm{ord}_{\delta(\mathrm{Frob}\,v)}(R_2\text{-residue of } f)$. `hRL` is `RegularityLaw`, two clauses for such $f$: at a fixed affine place $v$, if $\mathrm{ord}_V f \ge 0$ for all $V$ with $\mathrm{red}_1 V = v$, then the order of the $R_1$-residue at $v$ and the order of the $R_2$-residue at $\delta(\mathrm{Frob}\,v)$ are $\ge 0$ whenever these residues are nonzero; and at a node pair $s \in SS$, if $\mathrm{ord}_V f \ge 0$ for all $V$ with $\mathrm{red}_1 V = s_1$, then the two residues take a common value $c \in \kappa$ at $s_1$ and $s_2$. `hNV` is `NodeValueLaw`: for such $f$ and $s \in SS$, if no place $V$ of $F$ with $\mathrm{ord}_V f \neq 0$ has both $\mathrm{red}_1 V = s_1$ and $\mathrm{red}_2 V = s_2$, then the two residues take a common nonzero value at $s_1$ and $s_2$.
--
--   Compatibilities. `hα_coe` says $\alpha$ does not change $q$-expansions; `hβ_coe` says $\beta$ acts on $q$-expansions by `qExpand _ p`, i.e. $q \mapsto q^{p}$; `hθgal` says $\theta$ commutes with the arithmetic Galois action of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ on $F$; `hβθ` says $\beta$ is $\alpha$ followed by $\theta$.
--
--   Two-point pole laws `hLFst` and `hLSnd`. In the first-side version: for places $Q \ne Q'$ of $F$, both strict of the first kind, with the same first reduction, that common reduction being an affine place, for every natural number $n$ whose image in $\kappa$ is nonzero, for every $g \in R_1$.`integers` with nonzero $R_1$-residue such that $\mathrm{ord}_Q g = -n$, $\mathrm{ord}_{Q'} g = n$ and $\mathrm{ord}_W g = 0$ for every other strict first-kind place $W$ with the same first reduction, and for every $e \in A$ and every $\varepsilon \in R_1$.`integers` with nonzero $R_1$-residue such that $g = 1 + e\,\varepsilon$, the order of the $R_1$-residue of $\varepsilon$ at $\mathrm{red}_1 Q$ is at least $-1$. `hLSnd` is the same statement with `IsStrictSnd`, $\mathrm{red}_2$ and $R_2$ throughout.
--
--   Modular unit hypothesis `hUnit`. There exist $u_1, u_2 \in F$ and divisors $D_1, D_2$ with $D_1(W) = \mathrm{ord}_W u_1$ and $D_2(W) = \mathrm{ord}_W u_2$ for all $W$, such that: $u_1$ and $u_1^{-1}$ lie in $R_1$.`integers` with the $R_1$-residue of $u_1$ nonzero, for every place $v$ of $\bar F$ that is not $\delta$-Frobenius fixed the pushforward under $\mathrm{red}_1$ of the strict-first part of $D_1$ takes at $v$ the value $\mathrm{ord}_v$ of the $R_1$-residue of $u_1$, and for every place $C$ of $F$ on the infinity side (`IsInftySide`) the pushforward under $\mathrm{red}_1$ of the restriction of $D_1$ to the infinity-side places takes at $\mathrm{red}_1 C$ the value $\mathrm{ord}_{\mathrm{red}_1 C}$ of that residue; every nonzero $f \in F$ admits $m \neq 0$ and $j \in \mathbb{Z}$ with $f^{m}u_1^{j} \in R_2$.`integers` of nonzero $R_2$-residue; and the mirror-image conditions for $u_2$, with $R_2$, the strict-second part of $D_2$, $\mathrm{red}_2$, the zero side (`IsZeroSide`), and with every nonzero $f$ admitting $m \neq 0$, $j$ with $f^{m}u_2^{j} \in R_1$.`integers` of nonzero $R_1$-residue.
--
--   Cusp cover `hcusp`. Every place $w$ of $\bar F$ that is not affine is the first reduction of some infinity-side place of $F$ and also the second reduction of some zero-side place of $F$.
--
--   Configuration. Finally, given are natural numbers $d_1, d_2$, families $Q_1 : \mathrm{Fin}\,d_1 \to$ places of $F$ and $Q_2 : \mathrm{Fin}\,d_2 \to$ places of $F$, strict of the first and of the second kind respectively (`hQ₁`, `hQ₂`), with $i \mapsto \mathrm{red}_1(Q_1 i)$ and $j \mapsto \mathrm{red}_2(Q_2 j)$ injective (`hinj₁`, `hinj₂`), finite sets $T_1, T_2$ of places of $\bar F$ consisting exactly of the values of these two reductions (`hT₁`, `hT₂`), with $T_1$ disjoint from the set of first coordinates of $SS$ (`hT₁W`) and all members of $T_1$ and of $T_2$ affine (`hT₁aff`, `hT₂aff`); two general-position hypotheses: any $h \in \bar F$ with $\mathrm{ord}_v h \ge 0$ off $T_1$, $\mathrm{ord}_v h \ge -1$ on $T_1$ and value $0$ at every first coordinate of a node pair is zero (`hgp₁`), and any $h \in \bar F$ with $\mathrm{ord}_v h \ge 0$ off $T_2$ and $\mathrm{ord}_v h \ge -1$ on $T_2$ lies in the image of $\kappa$ (`hgp₂`); and the numerical condition $d_1 + d_2 =$ `genusFF` $(\overline{\mathbb{Q}}, F)$ (`hdeg`). Lastly, $D$ is a degree-zero divisor on $F$ which is good (`hgood`: every place in the support of $D$ is strict of the first or of the second kind), whose gluing datum `Psp.glueData α β hα hβ δ SS D` — the pair consisting of the $\mathrm{red}_1$-pushforward of the strict-first part of $D$ and the $\mathrm{red}_2$-pushforward of the strict-second part, with trivial constants — is admissible for $SS$ (`hadm`) and has trivial class in `GluedPic0 SS` (`hmk`).
--
--   Conclusion. There exist families $Q_1' : \mathrm{Fin}\,d_1 \to$ places of $F$ and $Q_2' : \mathrm{Fin}\,d_2 \to$ places of $F$ such that: every $Q_1'(i)$ is strict of the first kind; every $Q_2'(j)$ is strict of the second kind; $\mathrm{red}_1(Q_1'(i)) = \mathrm{red}_1(Q_1(i))$ for every $i$; $\mathrm{red}_2(Q_2'(j)) = \mathrm{red}_2(Q_2(j))$ for every $j$; and the divisor
--   $$\Bigl(\sum_i Q_1'(i) + \sum_j Q_2'(j)\Bigr) - \Bigl(\sum_i Q_1(i) + \sum_j Q_2(j)\Bigr),$$
--   formed from the indicated sums of single places with multiplicity one, has degree zero, and its class in `Pic0` equals the class of $D$.
--
--   This is the existence of a two-sided representative, with prescribed reductions, of a degree-zero divisor class on $X_H(M)$ over $\overline{\mathbb{Q}}$ whose glued class on the semistable special fibre at $p$ vanishes: the class of $D$ is realised by moving the $g = d_1 + d_2$ prescribed strict places within their fibres over the reduced curve. It is invoked in [`ModularCurve.JHPlaceSpecialization.exists_principal_degZero_forall_support_sub_inertia_smul_eq_of_splitting`](thm.html#ModularCurve.JHPlaceSpecialization.exists_principal_degZero_forall_support_sub_inertia_smul_eq_of_splitting), in the analysis of the specialisation of $J_H(M)$ at $p$ that underlies the level-lowering step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHPlaceSpecialization_ProlongationDatum_IsModel_exists_isStrictFst_isStrictSnd_reduceFst_eq_reduceSnd_eq_pic0Mk_eq_of_isGoodDiv_of_gammaLift_of_unit_of_cusp.lean

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

theorem ModularCurve.JHPlaceSpecialization.ProlongationDatum.IsModel.exists_isStrictFst_isStrictSnd_reduceFst_eq_reduceSnd_eq_pic0Mk_eq_of_isGoodDiv_of_gammaLift_of_unit_of_cusp
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
    (hgp₁ : ∀ h : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), (∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), v ∉ T₁ → 0 ≤ v.ord h) → (∀ v ∈ T₁, -1 ≤ v.ord h) → (∀ w ∈ (SS.image Prod.fst), w.HasValue h 0) → h = 0)
    (hgp₂ : ∀ h : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), (∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), v ∉ T₂ → 0 ≤ v.ord h) → (∀ v ∈ T₂, -1 ≤ v.ord h) → ∃ c : (ResidueField ↥A), h = algebraMap (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) c)
    (hdeg : d₁ + d₂ = genusFF (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H))))
    (hgood : Psp.IsGoodDiv α β hα hβ δ (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)))
    (hadm : Psp.glueData α β hα hβ δ SS (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) ∈ GluingData.admissible SS)
    (hmk : GluedPic0.mk SS ⟨Psp.glueData α β hα hβ δ SS (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), hadm⟩ = 0) :
    ∃ (Q₁' : Fin d₁ → Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (Q₂' : Fin d₂ → Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)),
      (∀ i, Psp.IsStrictFst α β hα hβ δ (Q₁' i)) ∧ (∀ j, Psp.IsStrictSnd α β hα hβ δ (Q₂' j)) ∧
      (∀ i, Psp.reduceFst α hα (Q₁' i) = Psp.reduceFst α hα (Q₁ i)) ∧
      (∀ j, Psp.reduceSnd β hβ δ (Q₂' j) = Psp.reduceSnd β hβ δ (Q₂ j)) ∧
      ∃ hdeg0 : ((∑ i, Finsupp.single (Q₁' i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂' j) (1 : ℤ))
          - (∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ)) : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) ∈ Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)),
        Pic0.mk ⟨_, hdeg0⟩ = Pic0.mk D := by sorry
