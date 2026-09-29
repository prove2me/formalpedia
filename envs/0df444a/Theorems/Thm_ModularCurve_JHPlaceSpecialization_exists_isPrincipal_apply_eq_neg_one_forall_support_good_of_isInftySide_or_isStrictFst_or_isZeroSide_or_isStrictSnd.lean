-- Prove2me | Theorems.Thm_ModularCurve_JHPlaceSpecialization_exists_isPrincipal_apply_eq_neg_one_forall_support_good_of_isInftySide_or_isStrictFst_or_isZeroSide_or_isStrictSnd
-- name    : ModularCurve.JHPlaceSpecialization.exists_isPrincipal_apply_eq_neg_one_forall_support_good_of_isInftySide_or_isStrictFst_or_isZeroSide_or_isStrictSnd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/87c5e28c-6c6b-52e4-85c8-a82c449bebc2
-- title:
--   Removability of a bad place on either branch
-- statement:
--   Throughout, $p$ is a prime and $M$ a nonzero natural number with $p \mid M$ and $p^2 \nmid M$, and $H \le (\mathbb{Z}/M)^\times$ is a subgroup containing the kernel of the reduction map $(\mathbb{Z}/M)^\times \to (\mathbb{Z}/(M/p))^\times$ (hypothesis `hHp`: every unit sent to $1$ by `ZMod.unitsMap` for $M/p \mid M$ lies in $H$), with $M/p$ nonzero. Further, $A$ is a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` lying over $p$ in the sense of [`ValuationSubring.LiesOverPrime`](def/FLTPrelim_Ramification.html#L16) (that is, $p$ is a nonunit of $A$), and its residue field $\kappa =$ `ResidueField ↥A` is algebraically closed of characteristic $p$.
--
--   The three function fields involved are $F =$ `xHFunctionFieldBar M H`, the base change to $\overline{\mathbb{Q}}$ of the $q$-expansion field of level $M$ and character group $H$ inside $\overline{\mathbb{Q}}((q))$; $F' =$ `xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)`, the analogous field at level $M/p$ for the image `infSubgroup p M H hpM` of $H$; and $\mathbb{F} =$ `JHNeronObjectAtP.Fbar p M H hpM κ`, the $q$-expansion function field over $\kappa$ for the group `JHNeronObjectAtP.ΓN p M H hpM`. Places are [`AlgebraicCurve.Place`](def/AlgebraicCurve_DivisorClassGroup.html#L22), i.e. proper valuation subrings containing the base field and having principal ideal ring of integers, with `ord` the associated normalised order function, and divisors are finitely supported $\mathbb{Z}$-valued functions on places, `Divisor.degree` being the sum of the coefficients weighted by the residue degrees.
--
--   The data are: an automorphism $\theta$ of $F$ over $\overline{\mathbb{Q}}$; two integral $\overline{\mathbb{Q}}$-algebra maps $\alpha, \beta : F' \to F$ (integrality recorded by `hα`, `hβ`); a unit $pb$ of $\mathbb{Z}/(M/p)$ whose underlying element is $p$ (`hpb`); a self-map $\delta$ of the set of places of $\mathbb{F}$ over $\kappa$ which, by `hδ`, is the action on places of the semilinear automorphism attached to the diamond automorphism `diamondActionModL` evaluated at the lift [`CuspForm.gammaLift (M / p) pb`](def/CuspForm_HeckeOperatorFormsGammaH.html#L36) of $pb$ to $\Gamma_0(M/p)$; a finite set $SS$ of pairs of places of $\mathbb{F}$ which, by `hSS`, is exactly `ssNodePairsQExp`, i.e. the set of pairs $s$ with $s_2$ a supersingular place and $s_1$ the $q$-expansion Frobenius place `qExpFrobeniusPlaceModL` of $s_2$; a specialization datum $Psp$ of type `JHPlaceSpecialization p M H hpM A` (a map $sp$ from places of $F'$ to places of $\mathbb{F}$ together with a homomorphism on degree-zero Picard groups, surjectivity of $sp$, compatibility of $sp$ with $q$-expansions and with divisors of functions, equivariance for inertia and Frobenius of $A$, and compatibility of the two); and a prolongation datum $Rpd$ of type `JHPlaceSpecialization.ProlongationDatum Psp θ`, consisting of two regular prolongations $R_1, R_2$ of $A$ to $F$ with residues in $\mathbb{F}$, the $q$-expansion compatibility of the residue of $R_1$, and the identification of $R_2$ with the transport of $R_1$ along $\theta$ (membership in the integers of $R_2$ means that $\theta f$ lies in the integers of $R_1$, and the $R_2$-residue of $f$ is the $R_1$-residue of $\theta f$).
--
--   Write $\mathrm{red}_1 = Psp.\mathtt{reduceFst}\,\alpha$, namely $W \mapsto sp(W|_\alpha)$, and $\mathrm{red}_2 = Psp.\mathtt{reduceSnd}\,\beta\,\delta$, namely $W \mapsto \delta(sp(W|_\beta))$, where $W|_\alpha$, $W|_\beta$ denote restriction of a place of $F$ along $\alpha$, $\beta$. A place $v$ of $\mathbb{F}$ is `Fixed` for $\delta$ when $\Phi(\delta(\Phi(v))) = v$, with $\Phi$ the Frobenius place operator; $W$ is `IsStrictFst` when $\delta(\Phi(\mathrm{red}_1 W)) = \mathrm{red}_2 W$ and $\mathrm{red}_1 W$ is not fixed, and `IsStrictSnd` when $\mathrm{red}_1 W = \Phi(\mathrm{red}_2 W)$ and $\mathrm{red}_2 W$ is not fixed; `fstDiv` and `sndDiv` are the restrictions of a divisor to the places of the respective strict type.
--
--   The hypotheses fall into the following groups.
--
--   Structural laws: `hTD` is the type dichotomy, that every place $W$ of $F$ satisfies $\mathrm{red}_1 W = \Phi(\mathrm{red}_2 W)$ or $\delta(\Phi(\mathrm{red}_1 W)) = \mathrm{red}_2 W$; `hFix` says the set of $\delta$-fixed places of $\mathbb{F}$ is finite; `hmodel` is `Rpd.IsModel`, the conjunction of the two divisor laws (for $f$ in the integers of both prolongations with nonzero residues and $D$ the divisor of $f$, the $\mathrm{red}_1$-pushforward of the strict-first part of $D$ computes the order of the $R_1$-residue of $f$ at every non-fixed place, and symmetrically for $\mathrm{red}_2$, the strict-second part and the $R_2$-residue) and of the two cusp laws at the $\infty$-side and at the $0$-side; `hO` is `OrderLawFixed`, which at a fixed affine place $v$ expresses the $\mathrm{red}_1$-pushforward of the divisor of $f$ as the order of the $R_1$-residue at $v$ plus the order of the $R_2$-residue at $\delta(\Phi(v))$; `hRL` is `RegularityLaw` for $SS$ (nonnegativity of the two residue orders at fixed affine places under nonnegativity upstream, and existence of a common value of the two residues at each node pair of $SS$); `hNV` is `NodeValueLaw` for $SS$ (at a node pair $s$ not hit by the divisor of $f$, the two residues take a common nonzero value at $s_1$ and $s_2$).
--
--   Normalisations: `hα_coe` says $\alpha$ is the identity on $q$-expansions, `hβ_coe` says $\beta$ acts on $q$-expansions by `qExpand … p`, i.e. by $q \mapsto q^p$; `hθgal` says $\theta$ commutes with the arithmetic Galois action of $\mathrm{Aut}(\overline{\mathbb{Q}}/\mathbb{Q})$ on $F$; `hβθ` says $\beta$ is $\alpha$ followed by $\theta$.
--
--   Local order bounds `hLFst` and `hLSnd`: for `hLFst`, given two distinct places $Q \ne Q'$ of $F$ of strict first type with $\mathrm{red}_1 Q' = \mathrm{red}_1 Q$ and $\mathrm{red}_1 Q$ an affine place (in the sense of `IsAffinePlace`: some element of $\mathbb{F}$ with $q$-expansion `jqModC κ` has a value at it), a natural number $n$ nonzero in $\kappa$, an element $g$ of the integers of $R_1$ with nonzero $R_1$-residue such that $\mathrm{ord}_Q g = -n$, $\mathrm{ord}_{Q'} g = n$ and $\mathrm{ord}_W g = 0$ for every other strict-first place $W$ with the same $\mathrm{red}_1$-image, and a factorisation $g = 1 + e\varepsilon$ with $e \in A$ and $\varepsilon$ in the integers of $R_1$ with nonzero residue, the order at $\mathrm{red}_1 Q$ of the $R_1$-residue of $\varepsilon$ is at least $-1$; `hLSnd` is the same statement with the second type, $\mathrm{red}_2$ and $R_2$ throughout.
--
--   Modular units `hUnit`: there exist $u_1, u_2 \in F$ and divisors $D_1, D_2$ with $D_i W = \mathrm{ord}_W u_i$ for all $W$, such that (i) $u_1$ and $u_1^{-1}$ lie in the integers of $R_1$, the $R_1$-residue of $u_1$ is nonzero, at every non-fixed place $v$ of $\mathbb{F}$ the $\mathrm{red}_1$-pushforward of the strict-first part of $D_1$ equals the order at $v$ of that residue, and for every $\infty$-side place $C$ the $\mathrm{red}_1$-pushforward of the restriction of $D_1$ to $\infty$-side places, evaluated at $\mathrm{red}_1 C$, equals the order of that residue at $\mathrm{red}_1 C$; (ii) every nonzero $f \in F$ admits $m \ne 0$ and $j \in \mathbb{Z}$ with $f^m u_1^{\,j}$ in the integers of $R_2$ with nonzero $R_2$-residue; (iii) the mirror clauses for $u_2$, with $R_2$, $\mathrm{red}_2$, the strict-second part of $D_2$ and the $0$-side places; (iv) every nonzero $f \in F$ admits $m \ne 0$ and $j \in \mathbb{Z}$ with $f^m u_2^{\,j}$ in the integers of $R_1$ with nonzero $R_1$-residue. Here an $\infty$-side place of $F$ is one that is cuspidal for the $j$-expansion and at which $x'/x^p$ has a value with residue $1$, for $x, x'$ of $q$-expansions $j(q)$ and $j(q^p)$; a $0$-side place is cuspidal for $j(q^p)$ and $x/x'^p$ has a value with residue $1$.
--
--   Cusp fibres and orientation: `hcusp` says every non-affine place $w$ of $\mathbb{F}$ is both $\mathrm{red}_1 C$ for some $\infty$-side place $C$ and $\mathrm{red}_2 C$ for some $0$-side place $C$; `horientInf` says $\delta(\Phi(\mathrm{red}_1 C)) = \mathrm{red}_2 C$ for every $\infty$-side place $C$, and `horient0` says $\mathrm{red}_1 C = \Phi(\mathrm{red}_2 C)$ for every $0$-side place $C$.
--
--   Avoidance data: $S$ is a finite subset of $\kappa$ none of whose elements lies in `ssJSet p κ`, the set of $j$-invariants all of whose elliptic models have trivial $p$-torsion; $xj \in F$ has $q$-expansion `jqModC` over $\overline{\mathbb{Q}}$ and $xb \in \mathbb{F}$ has $q$-expansion `jqModC` over $\kappa$; $T$ is a finite set of places of $\mathbb{F}$ containing every place $t$ such that $xb$ is outside the valuation ring of $t$ or $\mathrm{ord}_t(xb - s) > 0$ for some $s \in S$.
--
--   Finally, $V_0$ is a place of $F$ which is bad in the sense of `hbad`: there is no $a \in A$ with $\mathrm{ord}_{V_0}(xj - a) > 0$ and residue of $a$ outside $S$; and `hside` assumes that $V_0$ is an $\infty$-side place or of strict first type, or a $0$-side place or of strict second type.
--
--   Under these hypotheses there exists a divisor $p'$ of $F$ over $\overline{\mathbb{Q}}$ such that: $p'$ is principal, i.e. there is a nonzero $f \in F$ with $p' V = \mathrm{ord}_V f$ for every place $V$; $p' V_0 = -1$; the degree of $p'$ is $0$; and every place $V$ in the support of $p'$ other than $V_0$ is good, i.e. there exists $a \in A$ with $\mathrm{ord}_V(xj - a) > 0$ and the residue of $a$ not in $S$.
--
--   This is the removal step of the avoidance argument for the curves $X_H(M)$ at a place dividing $M$ exactly once: a single bad place on the $\infty$-side/strict-first branch or on the $0$-side/strict-second branch can be cancelled by a principal divisor supported, away from that place, only at places whose $j$-value reduces outside the excluded finite set $S$. It merges the two branch lemmas `exists_isPrincipal_apply_eq_neg_one_forall_support_good_of_isInftySide_or_isStrictFst` and `exists_isPrincipal_apply_eq_neg_one_forall_support_good_of_isZeroSide_or_isStrictSnd` into the single dichotomy used by `exists_isPrincipal_apply_eq_neg_one_forall_support_good_of_not_good_of_coe_of_unit_of_cusp_of_orient`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHPlaceSpecialization_exists_isPrincipal_apply_eq_neg_one_forall_support_good_of_isInftySide_or_isStrictFst_or_isZeroSide_or_isStrictSnd.lean

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

theorem ModularCurve.JHPlaceSpecialization.exists_isPrincipal_apply_eq_neg_one_forall_support_good_of_isInftySide_or_isStrictFst_or_isZeroSide_or_isStrictSnd
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
    (hside : (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A) V₀ ∨ Psp.IsStrictFst α β hα hβ δ V₀) ∨
      (JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A) V₀ ∨ Psp.IsStrictSnd α β hα hβ δ V₀)) :
    ∃ p' : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
      Divisor.IsPrincipal p' ∧ p' V₀ = -1 ∧ Divisor.degree p' = 0 ∧
        ∀ V ∈ p'.support, V ≠ V₀ → (∃ a : ↥A, 0 < V.ord (xj - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a : AlgebraicClosure ℚ)) ∧ IsLocalRing.residue ↥A a ∉ S) := by sorry
