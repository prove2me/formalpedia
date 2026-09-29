-- Prove2me | Theorems.Thm_ModularCurve_JHPlaceSpecialization_ProlongationDatum_annulus_ord_residue_eq_one_and_endSlope_both_ends_of_forall_isUnit_evalAt_mem_integers
-- name    : ModularCurve.JHPlaceSpecialization.ProlongationDatum.annulus_ord_residue_eq_one_and_endSlope_both_ends_of_forall_isUnit_evalAt_mem_integers
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/9bfa5539-1250-5982-8bca-6e69f737234b
-- title:
--   End-slope law at both ends of a node annulus
-- statement:
--   Fix a prime $p$ (as a `Fact`) and $M$ with $M \neq 0$, $p \mid M$ and $M/p \neq 0$, a subgroup $H \le (\mathbb{Z}/M)^{\times}$, and a valuation subring $A$ of $\overline{\mathbb{Q}}$ whose residue field $\kappa$ has characteristic $p$ and is algebraically closed. Let $F_M$ denote `xHFunctionFieldBar M H`, the base change to $\overline{\mathbb{Q}}$ of the function field of $X_H(M)$ inside Laurent series, and $\bar F$ the field `JHNeronObjectAtP.Fbar p M H hpM κ`. Given a finite set $SS$ of ordered pairs of places of $\bar F$ over $\kappa$, a $\overline{\mathbb{Q}}$-algebra automorphism $\theta$ of $F_M$, a place specialisation $Psp$ and a prolongation datum $Rpd$ for $Psp$ and $\theta$ — in particular two regular prolongations $R_1,R_2$ of $A$ to $F_M$ with residue field $\bar F$, compatible via $f \in R_2 \iff \theta f \in R_1$ and $\overline{f}^{(2)} = \overline{\theta f}^{(1)}$ — fix $s \in SS$, with components $s_1 = s.1.1$ and $s_2 = s.1.2$, and an annulus $An$ for $A$ in $F_M$, with domain $An.\mathrm{dom}$ a set of places of $F_M$ over $\overline{\mathbb{Q}}$, parameter $z = An.\mathrm{param}$ and modulus $\pi = An.\mathrm{modulus}$ in the maximal ideal of $A$. Assume: $z$ lies in the integers of $R_2$ and its residue has order $1$ at $s_2$; the element $\pi \cdot z^{-1}$ (the image of $\pi$ under $\overline{\mathbb{Q}} \to F_M$ times $z^{-1}$) lies in the integers of $R_1$ and its residue has order $1$ at $s_1$; and, at each end, the unit-reading property: every nonzero $g \in F_M$ with $\operatorname{ord}_P g = 0$ for all $P \in An.\mathrm{dom}$ and with $P.\mathrm{evalAt}\,g$ lying in $A$ and a unit of $A$ for all such $P$ lies in the integers of $R_2$ (respectively $R_1$) with nonzero residue of order $0$ at $s_2$ (respectively $s_1$). The conclusion is the conjunction of two clauses. The first reasserts that $z$ lies in the integers of $R_2$ with $\operatorname{ord}_{s_2}$ of its residue equal to $1$, and adds: for every $f$ in the integers of $R_2$ with nonzero residue and with $\operatorname{ord}_P f = 0$ at every $P \in An.\mathrm{dom}$, and every such $P$, the value $P.\mathrm{evalAt}\,f \cdot (P.\mathrm{evalAt}\,z)^{-m}$, where $m = \operatorname{ord}_{s_2}$ of the residue of $f$, lies in $A$ and is a unit there. The second clause is the same statement with $R_2$, $z$, $s_2$ replaced by $R_1$, $\pi \cdot z^{-1}$, $s_1$.
--
--   This is the per-node attachment statement: it says that the annulus is attached, in the sense of end parameters whose residues are uniformisers together with the end-slope law $|f| = |c| \cdot |z|^{m}$ reading off the order of the residue at the corresponding branch, to $R_2$ at $s_2$ with parameter $z$ and to $R_1$ at $s_1$ with parameter $\pi/z$. It supplies the two attachment conjuncts used by [`ModularCurve.XHDRModelAtP.exists_width_annulus_attachedBothEnds_of_jHPlaceSpecialization_of_offDiag`](thm.html#ModularCurve.XHDRModelAtP.exists_width_annulus_attachedBothEnds_of_jHPlaceSpecialization_of_offDiag), where the hypotheses come from the étale crossing chart $uv = \pi$ of the Deligne–Rapoport model at a node.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHPlaceSpecialization_ProlongationDatum_annulus_ord_residue_eq_one_and_endSlope_both_ends_of_forall_isUnit_evalAt_mem_integers.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_ComponentGroup
import Definitions.Def_AlgebraicCurve_SemistableCharts

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve
  IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP
open scoped MatrixGroups

theorem ModularCurve.JHPlaceSpecialization.ProlongationDatum.annulus_ord_residue_eq_one_and_endSlope_both_ends_of_forall_isUnit_evalAt_mem_integers
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ))
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (SS : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) ×
      Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)

    (s : ↥SS) (An : AlgebraicCurve.Annulus A ↥(xHFunctionFieldBar M H))

    (hz₂ : ∃ h₂ : An.param ∈ Rpd.R₂.integers, s.1.2.ord (Rpd.R₂.residue ⟨An.param, h₂⟩) = 1)
    (hz₁ : ∃ h₁ : algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((An.modulus : ↥A) : AlgebraicClosure ℚ) * An.param⁻¹ ∈ Rpd.R₁.integers,
      s.1.1.ord (Rpd.R₁.residue ⟨_, h₁⟩) = 1)

    (hu₂ : ∀ g : ↥(xHFunctionFieldBar M H), g ≠ 0 → (∀ P ∈ An.dom, P.ord g = 0) → (∀ P ∈ An.dom, ∃ h : P.evalAt g ∈ A, IsUnit (⟨_, h⟩ : ↥A)) →
      ∃ hg : g ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨g, hg⟩ ≠ 0 ∧ s.1.2.ord (Rpd.R₂.residue ⟨g, hg⟩) = 0)
    (hu₁ : ∀ g : ↥(xHFunctionFieldBar M H), g ≠ 0 → (∀ P ∈ An.dom, P.ord g = 0) → (∀ P ∈ An.dom, ∃ h : P.evalAt g ∈ A, IsUnit (⟨_, h⟩ : ↥A)) →
      ∃ hg : g ∈ Rpd.R₁.integers, Rpd.R₁.residue ⟨g, hg⟩ ≠ 0 ∧ s.1.1.ord (Rpd.R₁.residue ⟨g, hg⟩) = 0) :
    (∃ h₂ : An.param ∈ Rpd.R₂.integers, s.1.2.ord (Rpd.R₂.residue ⟨An.param, h₂⟩) = 1 ∧
      ∀ (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨f, hf⟩ ≠ 0 →
        (∀ P ∈ An.dom, P.ord f = 0) → ∀ P ∈ An.dom,
          ∃ h : P.evalAt f * (P.evalAt An.param) ^ (-(s.1.2.ord (Rpd.R₂.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A)) ∧
    (∃ h₁ : algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((An.modulus : ↥A) : AlgebraicClosure ℚ) * An.param⁻¹ ∈ Rpd.R₁.integers,
      s.1.1.ord (Rpd.R₁.residue ⟨_, h₁⟩) = 1 ∧
      ∀ (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨f, hf⟩ ≠ 0 →
        (∀ P ∈ An.dom, P.ord f = 0) → ∀ P ∈ An.dom,
          ∃ h : P.evalAt f * (P.evalAt (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((An.modulus : ↥A) : AlgebraicClosure ℚ) * An.param⁻¹)) ^
            (-(s.1.1.ord (Rpd.R₁.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A)) := by sorry
