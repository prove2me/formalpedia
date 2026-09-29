-- Prove2me | Theorems.Thm_ModularCurve_JHPlaceSpecialization_ProlongationDatum_exists_isGoodDiv_forall_mem_support_good_le_degree_fstDiv_sndDiv
-- name    : ModularCurve.JHPlaceSpecialization.ProlongationDatum.exists_isGoodDiv_forall_mem_support_good_le_degree_fstDiv_sndDiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/359b80c1-ef32-52ef-bc21-77c4ebc9a129
-- title:
--   Effective good divisor of large degree in general position
-- statement:
--   Fix a prime $p$ and a nonzero natural number $M$ with $p \mid M$ and $p^2 \nmid M$, and a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit whose image under `ZMod.unitsMap` along $M/p \mid M$ is $1$ (hypothesis `hHp`); $M/p$ is nonzero. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ lying over $p$ in the sense that $p$ is a non-unit of $A$, and assume its residue field $\kappa =$ `ResidueField ↥A` is algebraically closed of characteristic $p$. Write $F =$ `xHFunctionFieldBar M H` for the base change to $\overline{\mathbb{Q}}$ of the function field `xHFunctionField M H` inside $\overline{\mathbb{Q}}((q))$, $F' =$ `xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)` for the corresponding field at level $M/p$ with $H$ pushed forward along reduction, and $\bar F =$ `JHNeronObjectAtP.Fbar p M H hpM κ` $=$ `qExpFunctionFieldC κ (JHNeronObjectAtP.ΓN p M H hpM)`.
--
--   The data are: an $\overline{\mathbb{Q}}$-algebra automorphism $\theta$ of $F$; two integral $\overline{\mathbb{Q}}$-algebra maps $\alpha, \beta : F' \to F$ (hypotheses `hα`, `hβ`); a unit $pb$ of $\mathbb{Z}/(M/p)$ whose underlying element is $p$ (hypothesis `hpb`); a self-map $\delta$ of the set of $\kappa$-places of $\bar F$, required by `hδ` to be the action on places of the semilinear automorphism `SemilinearAut.ofAlgAut` attached to the diamond automorphism `diamondActionModL κ (M/p) (infSubgroup p M H hpM)` evaluated at [`CuspForm.gammaLift (M/p) pb`](def/CuspForm_HeckeOperatorFormsGammaH.html#L36); a finite set $SS$ of pairs of $\kappa$-places of $\bar F$ which, by `hSS`, is exactly `ssNodePairsQExp κ (JHNeronObjectAtP.ΓN p M H hpM) p`, i.e. the set of pairs $s$ with $s_2$ supersingular and $s_1$ the Frobenius place `qExpFrobeniusPlaceModL` of $s_2$; a specialisation datum `Psp : JHPlaceSpecialization p M H hpM A`, carrying in particular a surjective map $\mathrm{sp}$ from $\overline{\mathbb{Q}}$-places of $F'$ to $\kappa$-places of $\bar F$ compatible with $q$-expansions, with divisors, with inertia and with Frobenius, together with a map on $\mathrm{Pic}^0$; and a prolongation datum `Rpd : Psp.ProlongationDatum θ`, consisting of two regular prolongations $R_1, R_2$ of $A$ from $F$ to $\bar F$, the identification of the $R_1$-residues of coefficientwise reductions of Laurent series over $A$, and the requirement that $R_2$-integrality and $R_2$-residues are those of $R_1$ transported by $\theta$. Throughout, `reduceFst` $= \mathrm{sp} \circ (\,\cdot\,|_\alpha)$ and `reduceSnd` $= \delta \circ \mathrm{sp} \circ (\,\cdot\,|_\beta)$ denote the two readings of a place of $F$ in $\bar F$, a place $W$ of $F$ is strict of the first kind (`IsStrictFst`) when $\delta(\mathrm{Frob}(\mathrm{reduceFst}\,W)) = \mathrm{reduceSnd}\,W$ and $\mathrm{reduceFst}\,W$ is not $\delta$-fixed, strict of the second kind (`IsStrictSnd`) when $\mathrm{reduceFst}\,W = \mathrm{Frob}(\mathrm{reduceSnd}\,W)$ and $\mathrm{reduceSnd}\,W$ is not $\delta$-fixed, and `fstDiv`, `sndDiv` are the restrictions of a divisor to the places of the first, resp. second, kind.
--
--   The hypotheses on these data fall into the following groups. Compatibility of the two readings: `hTD` (`TypeDichotomy`) asserts that every place of $F$ satisfies at least one of the two strictness equations above, and `hFix` asserts that the set of $\delta$-fixed places $v$ of $\bar F$ (those with $\mathrm{Frob}(\delta(\mathrm{Frob}\,v)) = v$) is finite. Laws of the model: `hmodel` (`IsModel`) is the conjunction of the two divisor laws — for $f \in F$ integral for both prolongations with nonzero residues, the pushforward under `reduceFst` of the first-kind part of $\mathrm{div}(f)$ reads off $\mathrm{ord}_v$ of the $R_1$-residue of $f$ at every non-fixed $v$, and symmetrically for `reduceSnd`, $R_2$ — and of the two cusp laws, the same identities for the parts of $\mathrm{div}(f)$ supported on infinity-side, resp. zero-side, places evaluated at the readings of such places; `hO` (`OrderLawFixed`) gives, at $\delta$-fixed affine places $v$, the equality of the pushforward of $\mathrm{div}(f)$ at $v$ with $\mathrm{ord}_v$ of the $R_1$-residue plus $\mathrm{ord}_{\delta(\mathrm{Frob}\,v)}$ of the $R_2$-residue; `hRL` (`RegularityLaw`, two clauses) gives non-negativity of these orders at fixed affine places, and the existence of common values at the pairs in $SS$, whenever $f$ has non-negative order at all places reducing to the relevant point; `hNV` (`NodeValueLaw`) gives, for $s \in SS$ and $f$ whose divisor avoids the pair $s$, a nonzero $c \in \kappa$ which is the value of the $R_1$-residue at $s_1$ and of the $R_2$-residue at $s_2$. Degeneracy normalisations: `hα_coe` and `hβ_coe` say that on $q$-expansions $\alpha$ is the inclusion and $\beta$ is $q \mapsto q^p$ (`qExpand`), `hθgal` says that $\theta$ commutes with the arithmetic Galois action of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ on $F$, and `hβθ` says $\beta = \theta \circ \alpha$. Pole bounds at colliding strict places: `hLFst` states that if $Q \ne Q'$ are strict of the first kind with the same `reduceFst`-reading, that reading being an affine place, if $n$ is a natural number nonzero in $\kappa$, if $g$ is $R_1$-integral with nonzero residue, $\mathrm{ord}_Q g = -n$, $\mathrm{ord}_{Q'} g = n$ and $\mathrm{ord}_W g = 0$ for every other place $W$ of the first kind with the same reading, and if $g = 1 + e\varepsilon$ with $e \in A$ and $\varepsilon$ $R_1$-integral with nonzero residue, then $-1 \le \mathrm{ord}_{\mathrm{reduceFst}\,Q}$ of the $R_1$-residue of $\varepsilon$; `hLSnd` is the same statement for the second kind, `reduceSnd` and $R_2$. Modular units: `hUnit` asserts the existence of $u_1, u_2 \in F$ and divisors $D_1, D_2$ with $D_i(W) = \mathrm{ord}_W u_i$ such that $u_1$ and $u_1^{-1}$ are $R_1$-integral with nonzero $R_1$-residue of $u_1$, the pushforward under `reduceFst` of the first-kind part of $D_1$ equals the order of that residue at every non-fixed place, and the pushforward of the restriction of $D_1$ to infinity-side places agrees with the same orders at the readings of infinity-side places; moreover every nonzero $f \in F$ admits $m \ne 0$ and $j \in \mathbb{Z}$ with $f^m u_1^{j}$ $R_2$-integral of nonzero residue; and symmetrically for $u_2$, $R_2$, `reduceSnd`, the second-kind part of $D_2$, zero-side places, and powers $f^m u_2^{j}$ being $R_1$-integral of nonzero residue. Cusps: `hcusp` states that every non-affine place $w$ of $\bar F$ is the `reduceFst`-reading of some infinity-side place and the `reduceSnd`-reading of some zero-side place.
--
--   Under these hypotheses, for every finite set $S \subseteq \kappa$, every finite set $B$ of $\kappa$-places of $\bar F$, every two such places $t_1, t_2$ and every integer $n$, there exists a divisor $E$ on $F$ (over $\overline{\mathbb{Q}}$) with the following five properties: $E(V) \ge 0$ for all $V$; $E$ is a good divisor, i.e. every $V$ in the support of $E$ is strict of the first or of the second kind; every $V$ in the support of $E$ satisfies, first, that for each $x_j \in F$ whose Laurent series is `jqModC`, the $q$-expansion of $j$, there is $a \in A$ with $0 < \mathrm{ord}_V(x_j - a)$ and residue of $a$ outside $S$, and second, that $\mathrm{reduceFst}\,V \notin B$, $\mathrm{reduceSnd}\,V \notin B$, $\mathrm{reduceFst}\,V \ne t_1$ and $\mathrm{reduceSnd}\,V \ne t_2$; and finally $n \le \deg$ of the pushforward under `reduceFst` of the first-kind part of $E$, and $n \le \deg$ of the pushforward under `reduceSnd` of the second-kind part of $E$.
--
--   This is the auxiliary general-position statement behind the common-unit constructions on $X_H(M)$ at a prime $p$ exactly dividing $M$: it produces effective divisors of arbitrarily large degree on both sides whose support consists of strict places with prescribed $j$-values and whose two readings avoid finitely many prescribed places. It is used by the three theorems producing a common unit with a prescribed pole of the first kind, of the second kind, and over a collision place, which in turn feed the comparison of the two reductions in the level-lowering argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHPlaceSpecialization_ProlongationDatum_exists_isGoodDiv_forall_mem_support_good_le_degree_fstDiv_sndDiv.lean

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

theorem ModularCurve.JHPlaceSpecialization.ProlongationDatum.exists_isGoodDiv_forall_mem_support_good_le_degree_fstDiv_sndDiv
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
    (S : Finset (ResidueField ↥A)) (B : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (t₁ t₂ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) (n : ℤ) :
    ∃ E : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), (∀ V, 0 ≤ E V) ∧ Psp.IsGoodDiv α β hα hβ δ E ∧
      (∀ V ∈ E.support,
        (∀ (xj : ↥(xHFunctionFieldBar M H)), ((xj : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ) →
          ∃ a : ↥A, 0 < V.ord (xj - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a : AlgebraicClosure ℚ)) ∧ IsLocalRing.residue ↥A a ∉ S) ∧
        Psp.reduceFst α hα V ∉ B ∧ Psp.reduceSnd β hβ δ V ∉ B ∧ Psp.reduceFst α hα V ≠ t₁ ∧ Psp.reduceSnd β hβ δ V ≠ t₂) ∧
      n ≤ Divisor.degree (Finsupp.mapDomain (Psp.reduceFst α hα) (Psp.fstDiv α β hα hβ δ E)) ∧
      n ≤ Divisor.degree (Finsupp.mapDomain (Psp.reduceSnd β hβ δ) (Psp.sndDiv α β hα hβ δ E)) := by sorry
