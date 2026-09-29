-- Prove2me | Theorems.Thm_ModularCurve_JHPlaceSpecialization_exists_isPrincipal_apply_eq_neg_one_forall_support_good_of_isZeroSide_or_isStrictSnd
-- name    : ModularCurve.JHPlaceSpecialization.exists_isPrincipal_apply_eq_neg_one_forall_support_good_of_isZeroSide_or_isStrictSnd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/a2ae0a06-602f-5e79-9ee2-bac0d07df552
-- title:
--   Removing a bad place of the second kind on X_H(M)
-- statement:
--   Throughout, $p$ is a prime with $p \mid M$ and $p^2 \nmid M$, and $H \le (\mathbb{Z}/M)^{\times}$ is a subgroup containing every unit whose image under `ZMod.unitsMap` for $M/p \mid M$ is trivial (hypothesis `hHp`). Further, $A$ is a valuation subring of $\overline{\mathbb{Q}}$ lying over $p$ in the sense that $p$ is a non-unit of $A$ (`hA`), its residue field $\kappa =$ `ResidueField ↥A` having characteristic $p$ and being algebraically closed. Write $F_M =$ `xHFunctionFieldBar M H` for the base change to $\overline{\mathbb{Q}}$ of the $\Gamma_H(M)$ $q$-expansion function field, $F_{M/p} =$ `xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)` for the corresponding field at level $M/p$ with group the image of $H$, and $\bar F =$ `JHNeronObjectAtP.Fbar p M H hpM κ` for the $q$-expansion function field over $\kappa$ attached to `JHNeronObjectAtP.ΓN p M H hpM`. Places are in the sense of `Place`: valuation subrings of the function field containing the image of the base field, proper and with principal ideals; `Place.ord` is the associated normalised integer valuation, and a divisor is a finitely supported integer function on places.
--
--   The correspondence data consist of a $\overline{\mathbb{Q}}$-algebra automorphism $\theta$ of $F_M$ and two integral $\overline{\mathbb{Q}}$-algebra maps $\alpha, \beta \colon F_{M/p} \to F_M$ (`hα`, `hβ`), together with the $q$-expansion readings `hα_coe` ($\alpha$ is the identity on $q$-expansions), `hβ_coe` ($\beta$ is $q \mapsto q^p$, i.e. `qExpand` at $p$), the equivariance `hθgal` of $\theta$ for the arithmetic Galois action of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ on $F_M$, and `hβθ`, which says that $\beta$ is $\alpha$ followed by $\theta$. The diamond datum is a unit $pb$ of $\mathbb{Z}/(M/p)$ whose underlying residue is $p$ (`hpb`) and a self-map $\delta$ of the places of $\bar F$ over $\kappa$ which, by `hδ`, acts as the semilinear automorphism coming from `diamondActionModL` applied to a $\Gamma_0(M/p)$-lift of $pb$. The finite set $SS$ of pairs of places of $\bar F$ is, by `hSS`, exactly `ssNodePairsQExp`: pairs whose second entry is a supersingular place and whose first entry is its image under the mod-$p$ Frobenius place map `qExpFrobeniusPlaceModL`.
--
--   The specialisation kit is a term $P_{\mathrm{sp}} =$ `Psp` of `JHPlaceSpecialization p M H hpM A` (a map $\mathrm{sp}$ from places of $F_{M/p}$ to places of $\bar F$ together with a map on $\mathrm{Pic}^0$ and the compatibility, surjectivity, inertia and Frobenius axioms of that structure) and a prolongation datum `Rpd` for $P_{\mathrm{sp}}$ and $\theta$, consisting of two regular prolongations $R_1, R_2$ of $A$ from $F_M$ to $\bar F$ with the $q$-expansion reading of $R_1$-residues and the identification of $R_2$ with $R_1$ transported by $\theta$. From these one forms $\mathrm{reduceFst} = \mathrm{sp} \circ (\cdot|_{\alpha})$, $\mathrm{reduceSnd} = \delta \circ \mathrm{sp} \circ (\cdot|_{\beta})$, the predicates `IsStrictFst` ($\delta(\mathrm{Frob}(\mathrm{reduceFst}\,W)) = \mathrm{reduceSnd}\,W$ and $\mathrm{reduceFst}\,W$ is not `Fixed`) and `IsStrictSnd` ($\mathrm{reduceFst}\,W = \mathrm{Frob}(\mathrm{reduceSnd}\,W)$ and $\mathrm{reduceSnd}\,W$ is not `Fixed`), and the filtered divisors `fstDiv`, `sndDiv`. The law block is: `hTD`, every place satisfies one of the two alternatives of `TypeDichotomy`; `hFix`, the set of places fixed by $\mathrm{Frob} \circ \delta \circ \mathrm{Frob}$ is finite; `hmodel`, the conjunction of the two divisor laws and the two cusp laws (`IsModel`); `hO`, the order law at fixed affine places; `hRL`, the regularity law relative to $SS$; and `hNV`, the node value law relative to $SS$.
--
--   Two local pole laws are assumed. `hLFst` states: for strict-first places $Q \neq Q'$ with the same image under $\mathrm{reduceFst}$, this image being an affine place (`IsAffinePlace`: a place having a finite value on an element whose $q$-expansion is the $j$-function), for every $n \in \mathbb{N}$ nonzero in $\kappa$, every $g$ in the integers of $R_1$ with nonzero $R_1$-residue such that $\mathrm{ord}_Q g = -n$, $\mathrm{ord}_{Q'} g = n$ and $\mathrm{ord}_W g = 0$ for all other strict-first $W$ over the same image, and every $e \in A$ and $\varepsilon$ in the integers of $R_1$ with nonzero residue satisfying $g = 1 + e\varepsilon$, one has $-1 \le \mathrm{ord}_{\mathrm{reduceFst}\,Q}$ of the $R_1$-residue of $\varepsilon$. The hypothesis `hLSnd` is the same statement with `IsStrictFst`, $\mathrm{reduceFst}$ and $R_1$ replaced throughout by `IsStrictSnd`, $\mathrm{reduceSnd}$ and $R_2$.
--
--   The common-unit hypothesis `hUnit` asserts the existence of $u_1, u_2 \in F_M$ and divisors $D_1, D_2$ with $D_i(W) = \mathrm{ord}_W u_i$ for all $W$, such that: $u_1$ lies in the integers of $R_1$ with nonzero residue and with $u_1^{-1}$ also in those integers, the push-forward under $\mathrm{reduceFst}$ of the strict-first part of $D_1$ agrees at every non-fixed place $v$ with $\mathrm{ord}_v$ of the $R_1$-residue of $u_1$, and the push-forward under $\mathrm{reduceFst}$ of the infinity-side part of $D_1$ agrees at $\mathrm{reduceFst}\,C$, for every infinity-side $C$, with $\mathrm{ord}_{\mathrm{reduceFst}\,C}$ of that residue; moreover every nonzero $f \in F_M$ admits $m \neq 0$ and $j \in \mathbb{Z}$ with $f^m u_1^{j}$ in the integers of $R_2$ with nonzero residue. Symmetrically, $u_2$ is a unit of $R_2$ with nonzero residue, whose divisor satisfies the corresponding two identities for $\mathrm{reduceSnd}$, the strict-second part of $D_2$ and the zero-side part of $D_2$, and every nonzero $f$ admits $m \neq 0$ and $j \in \mathbb{Z}$ with $f^m u_2^{j}$ in the integers of $R_1$ with nonzero residue. Here infinity-side and zero-side are `IsInftySide` and `IsZeroSide`: cuspidality for the $j$-function, respectively for $j(q^p)$, together with a place value $\tau$ with residue $1$ on $x'/x^p$, respectively on $x/x'^p$, where $x$ and $x'$ have $q$-expansions $j$ and $j(q^p)$.
--
--   Finally, `hcusp` requires that every non-affine place of $\bar F$ be both $\mathrm{reduceFst}$ of some infinity-side place and $\mathrm{reduceSnd}$ of some zero-side place; the orientation hypotheses require $\delta(\mathrm{Frob}(\mathrm{reduceFst}\,C)) = \mathrm{reduceSnd}\,C$ for infinity-side $C$ (`horientInf`) and $\mathrm{reduceFst}\,C = \mathrm{Frob}(\mathrm{reduceSnd}\,C)$ for zero-side $C$ (`horient0`). The avoidance data are: a finite set $S \subseteq \kappa$ of residues none of which lies in `ssJSet p κ`, the set of those $j$ for which every elliptic Weierstrass curve of invariant $j$ has trivial $p$-torsion (`hS`); elements $x_j \in F_M$ with $q$-expansion the $j$-series `jqModC` over $\overline{\mathbb{Q}}$ and $\bar x \in \bar F$ with $q$-expansion `jqModC` over $\kappa$; and a finite set $T$ of places of $\bar F$ containing every place $t$ such that either $\bar x \notin t$ or $\mathrm{ord}_t(\bar x - s) > 0$ for some $s \in S$ (`hT`). Lastly, $V_0$ is a place of $F_M$ which is bad, in the sense that there is no $a \in A$ with $\mathrm{ord}_{V_0}(x_j - a) > 0$ and residue of $a$ outside $S$ (`hbad`), and which is either zero-side or strict-second (`hside`).
--
--   Under all these hypotheses there exists a divisor $p'$ on $F_M$ over $\overline{\mathbb{Q}}$ such that: $p'$ is principal, i.e. there is a nonzero $f \in F_M$ with $p'(V) = \mathrm{ord}_V f$ for every place $V$; $p'(V_0) = -1$; the degree of $p'$ is $0$; and every $V$ in the support of $p'$ other than $V_0$ is good, i.e. there is $a \in A$ with $\mathrm{ord}_V(x_j - a) > 0$ and residue of $a$ not in $S$.
--
--   This is the second-kind half of the step that moves a principal divisor off bad places on $X_H(M)$ at a prime exactly dividing the level: a place which is bad for the $j$-avoidance condition and lies on the zero side of the cuspidal region, or is strict of the second kind, can be cut out with multiplicity $-1$ by a principal divisor whose remaining support is good. It is combined with the corresponding first-kind statement in [`ModularCurve.JHPlaceSpecialization.exists_isPrincipal_apply_eq_neg_one_forall_support_good_of_isInftySide_or_isStrictFst_or_isZeroSide_or_isStrictSnd`](thm.html#ModularCurve.JHPlaceSpecialization.exists_isPrincipal_apply_eq_neg_one_forall_support_good_of_isInftySide_or_isStrictFst_or_isZeroSide_or_isStrictSnd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHPlaceSpecialization_exists_isPrincipal_apply_eq_neg_one_forall_support_good_of_isZeroSide_or_isStrictSnd.lean

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

theorem ModularCurve.JHPlaceSpecialization.exists_isPrincipal_apply_eq_neg_one_forall_support_good_of_isZeroSide_or_isStrictSnd
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
    (hside : JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A) V₀ ∨ Psp.IsStrictSnd α β hα hβ δ V₀) :
    ∃ p' : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
      Divisor.IsPrincipal p' ∧ p' V₀ = -1 ∧ Divisor.degree p' = 0 ∧
        ∀ V ∈ p'.support, V ≠ V₀ → (∃ a : ↥A, 0 < V.ord (xj - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a : AlgebraicClosure ℚ)) ∧ IsLocalRing.residue ↥A a ∉ S) := by sorry
