-- Prove2me | Theorems.Thm_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators
-- name    : ModularCurve.DRModel.exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.564058+00:00
-- url     : https://prove2.me/theorems/d017248b-786c-5758-bf88-f2fe5cd236b8
-- title:
--   Geometric fibre at p: two rational components, supersingular intersection
-- statement:
--   Let $p$ be a prime with $5 \le p$, and let $F$ be the subfield `modularFunctionFieldFull p` of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the series $j(q^{d})$ for the divisors $d$ of $p$, with distinguished element $j =$ `IgusaScheme.jFull p`. Let $j_p$ be an element of the finite chart algebra $A =$ `chartAlgFin ℤ F j` (the elements of $F$ integral over $\mathbb{Z}[j]$) whose $q$-expansion is $j(q^{p})$. Let $W_0 \ne W_1$ be valuation subrings of $F$ in each of which $p$ is a non-unit, such that for each $i$ and each $P \in \mathbb{Z}[X]$ with $P \bmod p \ne 0$ both $P(j)$ and $P(j)^{-1}$ lie in $W_i$, and such that any valuation subring of $F$ with these two properties is $W_0$ or $W_1$; assume $j_p - j^{p}$ is a non-unit of $W_0$, that every $x \in W_0$ satisfies $xQ(j) - P(j) \in \mathfrak{m}_{W_0}$ for some $P, Q \in \mathbb{Z}[X]$ with $Q \bmod p \ne 0$, and likewise for $W_1$ with $j_p$ in place of $j$. Let $\kappa$ be an algebraically closed field of characteristic $p$. Then there exist a curve model $M$ of $\kappa(X)$ over $\kappa$ — an integral scheme $M.C$ with a proper, smooth morphism of relative dimension $1$ to $\operatorname{Spec}\kappa$, an identification of its function field with `RatFunc κ` over $\kappa$, a bijection between its closed points and the places of $\kappa(X)/\kappa$ matching stalks with valuation subrings, and the property that every finite set of points lies in an affine open — and two morphisms $c_\infty, c_0$ from $M.C$ to the pullback of `DRModel.toBase p` along $\operatorname{Spec}(\mathbb{Z} \to \kappa)$, where `DRModel p` is the pushout of the two chart spectra $\operatorname{Spec}$ `chartAlgFin` and $\operatorname{Spec}$ `chartAlgInf` over $\operatorname{Spec}\mathbb{Z}$, such that: both commute with the projection to $\operatorname{Spec}\kappa$ and $M.\mathrm{toBase}$; both are closed immersions; every point of the fibre lies in the image of $c_\infty$ or of $c_0$; the two images are distinct; the fibre product of $c_\infty$ and $c_0$ is reduced and its cardinality equals that of `ssJSet p κ`, the set of $j \in \kappa$ such that every elliptic curve over $\kappa$ with that $j$-invariant has no non-zero point killed by $p$; and, for every $\mathbb{Z}$-algebra homomorphism $\psi$ from $A^{\infty} =$ `chartAlgInf ℤ F j` (the elements of $F$ integral over $\mathbb{Z}[j^{-1}]$) to $\mathbb{Z}$ and every section $\varepsilon$ of `DRModel.toBase p` over $\operatorname{Spec}\mathbb{Z}$ factoring as $\operatorname{Spec}\psi$ followed by the inclusion `ιInf` of the infinity chart, the $\kappa$-point `DRModel.sectionFibre ε (algebraMap ℤ κ)` of the fibre has image contained in that of $c_\infty$ if $p \mid \psi(a)$ for all $a \in A^{\infty}$ lying in $\mathfrak{m}_{W_0}$, image contained in that of $c_0$ if $p \mid \psi(a)$ for all such $a$ lying in $\mathfrak{m}_{W_1}$, image disjoint from that of $c_0$ if $p \nmid \psi(a)$ for some $a \in A^{\infty} \cap \mathfrak{m}_{W_1}$, and image disjoint from that of $c_\infty$ if $p \nmid \psi(a)$ for some $a \in A^{\infty} \cap \mathfrak{m}_{W_0}$.
--
--   This is the Deligne–Rapoport description of the fibre at $p$ of the model of $X_0(p)$ over $\mathbb{Z}$ — two copies of the $j$-line crossing transversally at the supersingular points — packaged together with the information of which of the two components a $\mathbb{Z}$-point of the pole chart reduces onto, the component $c_\infty$ being pinned by the valuation ring $W_0$. It feeds [`ModularCurve.exists_dRModelPackage_ffPin`](thm.html#ModularCurve.exists_dRModelPackage_ffPin), which assembles the model of $X_0(p)$ in the form required for the study of its reduction at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackage

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve AlgebraicCurve

theorem ModularCurve.DRModel.exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators
    (p : ℕ) [Fact p.Prime] [NeZero p] (hp : 5 ≤ p)
    (jp : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))
    (hjp : ((jp : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ) = qExpand ℚ p jq)
    (W₀ W₁ : ValuationSubring ↥(modularFunctionFieldFull p))
    (hp₀ : ((p : ℕ) : ↥(modularFunctionFieldFull p)) ∈ W₀.nonunits)
    (hp₁ : ((p : ℕ) : ↥(modularFunctionFieldFull p)) ∈ W₁.nonunits)
    (hne : W₀ ≠ W₁)
    (hgen : ∀ i : Fin 2, ∀ P : Polynomial ℤ, P.map (Int.castRingHom (ZMod p)) ≠ 0 →
        Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull p)) (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) P
            ∈ (![W₀, W₁] i) ∧
        (Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull p)) (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) P)⁻¹
            ∈ (![W₀, W₁] i))
    (hcomplete : ∀ V : ValuationSubring ↥(modularFunctionFieldFull p),
        ((p : ℕ) : ↥(modularFunctionFieldFull p)) ∈ V.nonunits →
        (∀ P : Polynomial ℤ, P.map (Int.castRingHom (ZMod p)) ≠ 0 →
          Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull p)) (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) P ∈ V ∧
          (Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull p)) (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) P)⁻¹ ∈ V) →
        V = W₀ ∨ V = W₁)
    (ht : ((jp : ↥(modularFunctionFieldFull p)) - (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) ^ p) ∈ W₀.nonunits)
    (hres₀ : ∀ x : ↥(modularFunctionFieldFull p), x ∈ W₀ → ∃ P Q : Polynomial ℤ, Q.map (Int.castRingHom (ZMod p)) ≠ 0 ∧
        x * Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull p)) (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) Q -
          Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull p)) (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) P
            ∈ W₀.nonunits)
    (hres₁ : ∀ x : ↥(modularFunctionFieldFull p), x ∈ W₁ → ∃ P Q : Polynomial ℤ, Q.map (Int.castRingHom (ZMod p)) ≠ 0 ∧
        x * Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull p)) (jp : ↥(modularFunctionFieldFull p)) Q -
          Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull p)) (jp : ↥(modularFunctionFieldFull p)) P
            ∈ W₁.nonunits)
    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] [DecidableEq κ] :
    ∃ (M : CurveModel κ (RatFunc κ))
      (cInf cZero : M.C ⟶ pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ)))),
      cInf ≫ pullback.snd _ _ = M.toBase ∧ cZero ≫ pullback.snd _ _ = M.toBase ∧
      IsClosedImmersion cInf ∧ IsClosedImmersion cZero ∧
      (∀ x : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ)))),
          x ∈ Set.range cInf.base ∨ x ∈ Set.range cZero.base) ∧
      Set.range cInf.base ≠ Set.range cZero.base ∧
      IsReduced (pullback cInf cZero) ∧
      Nat.card ↥(pullback cInf cZero) = Nat.card ↥(ssJSet p κ) ∧
      (∀ (ψ : ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) →ₐ[ℤ] ℤ)
         (ε : NeronModelInfra.SchemeHomOver (𝟙 (Spec (CommRingCat.of ℤ))) (DRModel.toBase p)),
         ε.1 = Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫
                 TwoChartIntegralModel.ιInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) →
         ((∀ a : ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)),
              (a : ↥(modularFunctionFieldFull p)) ∈ W₀.nonunits → (p : ℤ) ∣ ψ a) →
            Set.range (DRModel.sectionFibre ε (algebraMap ℤ κ)).base ⊆ Set.range cInf.base) ∧
         ((∀ a : ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)),
              (a : ↥(modularFunctionFieldFull p)) ∈ W₁.nonunits → (p : ℤ) ∣ ψ a) →
            Set.range (DRModel.sectionFibre ε (algebraMap ℤ κ)).base ⊆ Set.range cZero.base) ∧
         ((∃ a : ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)),
              (a : ↥(modularFunctionFieldFull p)) ∈ W₁.nonunits ∧ ¬ (p : ℤ) ∣ ψ a) →
            Disjoint (Set.range (DRModel.sectionFibre ε (algebraMap ℤ κ)).base) (Set.range cZero.base)) ∧
         ((∃ a : ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)),
              (a : ↥(modularFunctionFieldFull p)) ∈ W₀.nonunits ∧ ¬ (p : ℤ) ∣ ψ a) →
            Disjoint (Set.range (DRModel.sectionFibre ε (algebraMap ℤ κ)).base) (Set.range cInf.base))) := by sorry
