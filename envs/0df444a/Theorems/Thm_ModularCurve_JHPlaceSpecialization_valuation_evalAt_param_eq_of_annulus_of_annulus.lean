-- Prove2me | Theorems.Thm_ModularCurve_JHPlaceSpecialization_valuation_evalAt_param_eq_of_annulus_of_annulus
-- name    : ModularCurve.JHPlaceSpecialization.valuation_evalAt_param_eq_of_annulus_of_annulus
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/c508f22f-6f9c-54ce-a0f2-e1ba72d41130
-- title:
--   Depth at an inertia-fixed place is chart-independent
-- statement:
--   Fix a prime $p$ and $M$ with $p \mid M$ and $p^2 \nmid M$, and a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit that reduces to $1$ in $(\mathbb{Z}/(M/p))^\times$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a non-unit, whose residue field $\kappa$ is algebraically closed of characteristic $p$. Let $\theta$ be a $\overline{\mathbb{Q}}$-automorphism of $F_M := \overline{\mathbb{Q}}\cdot F(X_H(M))$ commuting with the arithmetic Galois action, $\alpha$ an integral $\overline{\mathbb{Q}}$-algebra map from the level-$(M/p)$ field for the image subgroup into $F_M$ which is the identity on underlying Laurent series, $\beta := \theta \circ \alpha$ (also integral), $pb$ a unit of $\mathbb{Z}/(M/p)$ represented by $p$, and $\delta$ the operator on places of $\mathrm{Fbar}$ given by translation under the mod-$\ell$ diamond automorphism attached to [`CuspForm.gammaLift (M / p) pb`](def/CuspForm_HeckeOperatorFormsGammaH.html#L36). Let $SS$ be a finset whose members are exactly the pairs $(\mathrm{Frob}(v), v)$ with $v$ supersingular, all supersingular places and their Frobenius images being `Fixed` for $\delta$. Let `Psp` be a place specialisation and `Rpd` a prolongation datum $(R_1,R_2)$ for it and $\theta$, subject to the type dichotomy, the model law, the order law at fixed places, and the regularity and node-value laws at $SS$ (summarised here). Let $e : SS \to \mathbb{N}$ be positive, $s \in SS$, and let $An$, $An'$ be annuli of $F_M$ over $A$ each satisfying: the domain consists of the places $W$ with $\mathrm{reduceFst}_\alpha(W) = s_1$ that are neither `IsStrictFst` nor `IsStrictSnd`; the modulus is $p^{e(s)}$ times a unit of $A$; the parameter is fixed by the inertia subgroup of $A$ over $\mathbb{Q}$; modulus$^{-1}$ times the parameter lies in $R_1$; the parameter lies in $R_2$ with non-zero residue, that residue having $\mathrm{ord}_{s_2} = 1$, and symmetrically modulus times the inverse parameter lies in $R_1$ with residue of $\mathrm{ord}_{s_1} = 1$; together with, on each side, the slope law that for $f$ in the relevant prolongation with non-zero residue and $\mathrm{ord}_P f = 0$ throughout the domain, $f(P)\cdot w(P)^{-\mathrm{ord}(\bar f)}$ is a unit of $A$ at every place $P$ of the domain, $w$ the corresponding parameter. Then for every place $V$ in the domain of $An$ fixed by the inertia subgroup, $A$-valuations agree: $v_A(V(\mathrm{param}\,An)) = v_A(V(\mathrm{param}\,An'))$.
--
--   This is the well-definedness of the depth of an inertia-fixed point in a node annulus of the semistable model of $X_H(M)$ at $p$: the valuation read off an admissible annulus chart attached to a node does not depend on the chart chosen. It feeds the construction of annulus depth data used in the description of the component group of the Néron model of $J_H(M)$ at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHPlaceSpecialization_valuation_evalAt_param_eq_of_annulus_of_annulus.lean

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_ComponentGroup
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_ModularCurve_JHNodeDepth

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JHNeronObjectAtP
open scoped MatrixGroups

theorem ModularCurve.JHPlaceSpecialization.valuation_evalAt_param_eq_of_annulus_of_annulus
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : (θ.toAlgHom.comp α).IsIntegral)
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v)
    (SS : Finset (Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))))
    (hSS : ∀ s, s ∈ SS ↔ s ∈ ssNodePairsQExp (ResidueField ↥A) (ΓN p M H hpM) p)
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)

    (hFix : ∀ y ∈ ssPlacesQExp (ResidueField ↥A) (ΓN p M H hpM) p,
      JHPlaceSpecialization.Fixed p M H hpM A δ y ∧
        JHPlaceSpecialization.Fixed p M H hpM A δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p y))
    (hTD : Psp.TypeDichotomy α (θ.toAlgHom.comp α) hα hβ δ)
    (hmodel : Rpd.IsModel α (θ.toAlgHom.comp α) hα hβ δ) (hO : Rpd.OrderLawFixed α (θ.toAlgHom.comp α) hα hβ δ)
    (hreg : Rpd.RegularityLaw α (θ.toAlgHom.comp α) hα hβ δ SS) (hnv : Rpd.NodeValueLaw α (θ.toAlgHom.comp α) hα hβ δ SS)

    (hθgal : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (f : ↥(xHFunctionFieldBar M H)),
      θ (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • f) =
        arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • θ f)
    (e : ↥SS → ℕ) (he : ∀ s, 0 < e s)
    (s : ↥SS) (An An' : AlgebraicCurve.Annulus A ↥(xHFunctionFieldBar M H))
    (hAn : ((∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
          W ∈ An.dom ↔ (Psp.reduceFst α hα W = s.1.1 ∧ ¬ Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W ∧ ¬ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ W)) ∧
        (∃ u : ↥A, IsUnit u ∧ An.modulus = ((p : ℕ) : ↥A) ^ (e s) * u) ∧
        (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.inertiaSubgroupIn ℚ →
          (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • An.param = An.param) ∧
        algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((An.modulus : AlgebraicClosure ℚ))⁻¹ * An.param ∈ Rpd.R₁.integers ∧
        (∃ h₂ : An.param ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨An.param, h₂⟩ ≠ 0) ∧

        (∃ h₂ : An.param ∈ Rpd.R₂.integers, s.1.2.ord (Rpd.R₂.residue ⟨An.param, h₂⟩) = 1 ∧
          ∀ (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨f, hf⟩ ≠ 0 →
            (∀ P ∈ An.dom, P.ord f = 0) → ∀ P ∈ An.dom,
              ∃ h : P.evalAt f * (P.evalAt An.param) ^ (-(s.1.2.ord (Rpd.R₂.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A)) ∧
        (∃ h₁ : algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((An.modulus : ↥A) : AlgebraicClosure ℚ) * An.param⁻¹ ∈ Rpd.R₁.integers,
          s.1.1.ord (Rpd.R₁.residue ⟨_, h₁⟩) = 1 ∧
          ∀ (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨f, hf⟩ ≠ 0 →
            (∀ P ∈ An.dom, P.ord f = 0) → ∀ P ∈ An.dom,
              ∃ h : P.evalAt f * (P.evalAt (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((An.modulus : ↥A) : AlgebraicClosure ℚ) * An.param⁻¹)) ^
                (-(s.1.1.ord (Rpd.R₁.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A))))
    (hAn' : ((∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
          W ∈ An'.dom ↔ (Psp.reduceFst α hα W = s.1.1 ∧ ¬ Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W ∧ ¬ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ W)) ∧
        (∃ u : ↥A, IsUnit u ∧ An'.modulus = ((p : ℕ) : ↥A) ^ (e s) * u) ∧
        (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.inertiaSubgroupIn ℚ →
          (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • An'.param = An'.param) ∧
        algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((An'.modulus : AlgebraicClosure ℚ))⁻¹ * An'.param ∈ Rpd.R₁.integers ∧
        (∃ h₂ : An'.param ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨An'.param, h₂⟩ ≠ 0) ∧

        (∃ h₂ : An'.param ∈ Rpd.R₂.integers, s.1.2.ord (Rpd.R₂.residue ⟨An'.param, h₂⟩) = 1 ∧
          ∀ (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨f, hf⟩ ≠ 0 →
            (∀ P ∈ An'.dom, P.ord f = 0) → ∀ P ∈ An'.dom,
              ∃ h : P.evalAt f * (P.evalAt An'.param) ^ (-(s.1.2.ord (Rpd.R₂.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A)) ∧
        (∃ h₁ : algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((An'.modulus : ↥A) : AlgebraicClosure ℚ) * An'.param⁻¹ ∈ Rpd.R₁.integers,
          s.1.1.ord (Rpd.R₁.residue ⟨_, h₁⟩) = 1 ∧
          ∀ (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨f, hf⟩ ≠ 0 →
            (∀ P ∈ An'.dom, P.ord f = 0) → ∀ P ∈ An'.dom,
              ∃ h : P.evalAt f * (P.evalAt (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((An'.modulus : ↥A) : AlgebraicClosure ℚ) * An'.param⁻¹)) ^
                (-(s.1.1.ord (Rpd.R₁.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A))))
    (V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (hV : V ∈ An.dom)
    (hVσ : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.inertiaSubgroupIn ℚ →
      (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • V = V) :
    A.valuation (V.evalAt An.param) = A.valuation (V.evalAt An'.param) := by sorry
