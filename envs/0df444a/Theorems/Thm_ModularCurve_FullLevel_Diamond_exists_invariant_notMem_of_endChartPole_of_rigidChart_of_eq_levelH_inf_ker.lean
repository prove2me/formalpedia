-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_Diamond_exists_invariant_notMem_of_endChartPole_of_rigidChart_of_eq_levelH_inf_ker
-- name    : ModularCurve.FullLevel.Diamond.exists_invariant_notMem_of_endChartPole_of_rigidChart_of_eq_levelH_inf_ker
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:30.533368+00:00
-- url     : https://prove2.me/theorems/653d9915-11b2-58ab-95cd-bb335fbd6fab
-- title:
--   Descent of a chart element avoiding Igusa-type valuation rings
-- statement:
--   Fix a prime $q$, a nonzero $M'$ with $q \nmid M'$, and a prime $\ell_g$ with $\ell_g \equiv 11 \pmod{12}$ and $\ell_g \mid M'$. Let $A$ be a valuation subring of $\overline{\mathbb Q}$ in which $q$ is a non-unit, let $W$ be a finite set of places of $\mathrm{modularFunctionFieldC}(\kappa_A, M')$ whose members are exactly the supersingular places (rational, affine geometric, and with $j$-value in $\mathrm{ssJSet}\,q$), let $R_0$ be a constant reduction of the base change to $\overline{\mathbb Q}$ of the full level-$M'$ modular function field towards its characteristic-$q$ analogue, compatible with coefficientwise reduction of Laurent series with coefficients in $A$, and let $s \in W$. Let $k_0 \subseteq \overline{\mathbb Q}$ be a subfield and $\pi_0 \in k_0$ an element of $A$ such that $A_0 := A \cap k_0$ is a discrete valuation ring with maximal ideal $(\pi_0)$. Let $H_1 \le (\mathbb Z/q^2M')^\times$ be the subgroup of units congruent to $1$ modulo $q$ and modulo $\ell_g$, let $K_\ell \subseteq k_0((t))$ be generated over $k_0$ by the image under the coefficient embedding of the function field of $X_{H_1}(q^2M')$, an $A_0$-algebra in a compatible tower, and let $j_\ell \in K_\ell$ be nonzero with Laurent expansion the $q$-expansion of $j$. Let $B$ be the chart algebra of elements of $K_\ell$ integral over $A_0[j_\ell]$ and $y \subset B$ a maximal ideal containing $\pi_0$, such that every homomorphism of $B$ to an algebraically closed field of characteristic $q$ with kernel $y$ carries $j_\ell$ to a supersingular $j$-invariant, and such that the specialisation compatibility $\mathtt{hover}$ holds: for $g$ in the level-$M'$ modular function field over $\mathbb Q$ whose base change lies in the integers of $R_0$, with non-negative order at every place where $j$ has non-negative order and with $R_0$-residue in the valuation ring of $s$, whenever $g \in K_\ell$ lies in $B$ and $c \in k_0 \cap A$ reduces to the value of the $R_0$-residue of $g$ at $s$, then $g - c \in y$. Assume moreover that $j(q\tau)$ lies in $K_\ell$ and in $B$ and is congruent modulo $y$ to some $a_0 \in A_0$, that $k_0$ contains a primitive $q$-th root of unity $\xi$, and that $G$ is a finite subgroup of $\mathrm{Aut}_{k_0}(K_\ell)$ each of whose elements $\tau$ satisfies $\mathrm{IsLevelAutAt}\,k_0\,q\,\xi\,q\,(q^2M')\,H_1\,\gamma^{-1}\,K_\ell\,\tau$ for some $\gamma \in \Gamma(q) \cap \Gamma_0(M')$. Let $K_0$ be the fixed field of $G$, let $\tilde O$ be a subring of $K_\ell$ and $O = \tilde O \cap K_0$, and let $B_x$ be a $G$-stable $A_0$-subalgebra of $K_\ell$. The hypothesis is that some $b \in B_x$ lies outside every valuation subring $V$ of $K_\ell$ whose elements of $k_0$ are exactly those of $A_0$, with $\pi_0$ in the maximal ideal of $V$, with $j_\ell \in V$ and no monic polynomial in $j_\ell$ over $A_0$ in the maximal ideal of $V$, and which omits some element of $\tilde O$. The conclusion is that some element $b$ of $B_x \cap K_0$ lies outside every valuation subring $V$ of $K_0$ whose elements of $k_0$ are exactly those of $A$, with $\pi_0$ in the maximal ideal of $V$, such that $j$ (the coefficient embedding of the $q$-expansion of $j$) lies in $K_0$ and in $V$ with no monic polynomial over $k_0$ with coefficients in $A$ evaluated at $j$ in the maximal ideal of $V$, and which omits some element of $O$.
--
--   This is the descent step of the node analysis at the $\Gamma_1(\ell_g)$-guarded auxiliary level: an element of a $G$-stable subalgebra of $K_\ell$ which avoids all Igusa-type valuation rings (constants $A_0$, $\pi_0$ a non-unit, $j$ residually transcendental) missing the end $\tilde O$ is replaced by an element of the fixed field $K_0$ with the corresponding property relative to $O = \tilde O \cap K_0$. It feeds the per-node trace conclusions [`ModularCurve.FullLevel.Diamond.pernodeConclusion_traces_of_rigidChart_linkedScalars_of_eq_three_of_dvd`](thm.html#ModularCurve.FullLevel.Diamond.pernodeConclusion_traces_of_rigidChart_linkedScalars_of_eq_three_of_dvd) and `…_of_eq_two_of_dvd`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_Diamond_exists_invariant_notMem_of_endChartPole_of_rigidChart_of_eq_levelH_inf_ker.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringW2
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_CoordRing
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_JqCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 12800000

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup AlgebraicCurve.TwoChartIntegralModel
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

theorem ModularCurve.FullLevel.Diamond.exists_invariant_notMem_of_endChartPole_of_rigidChart_of_eq_levelH_inf_ker
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')

    (ℓg : ℕ) (hℓg : ℓg.Prime) (hℓg12 : ℓg % 12 = 11) (hℓgM' : ℓg ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q M' (ResidueField A))
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    (s : ↥W)

    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (π₀ : ↥k₀) (hπ : (π₀ : (AlgebraicClosure ℚ)) ∈ A)
    (hdvr : IsDiscreteValuationRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hunif : maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) =
      Ideal.span {(⟨π₀, hπ⟩ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))})
    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓgM' (q ^ 2))).ker)
    (Kℓ : IntermediateField ↥k₀ (LaurentSeries ↥k₀))
    (hKℓ : Kℓ = ModularCurve.laurentBaseChange ↥k₀
      (ModularCurve.xHFunctionField (q ^ 2 * M') H₁))
    [Algebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ] [IsScalarTower ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ ↥Kℓ]
    (jℓ : ↥Kℓ) (hjℓ : ((jℓ : LaurentSeries ↥k₀)) = ModularCurve.coeffEmb ↥k₀ ModularCurve.jq) [Fact (jℓ ≠ 0)]
    (y : Ideal ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ)) (hy : y.IsMaximal)
    (hϖy : algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ) ⟨π₀, hπ⟩ ∈ y)
    (hss : ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
      (φ : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ) →+* Ω), RingHom.ker φ = y → φ (jChartFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ) ∈ ModularCurve.ssJSet q Ω)

    (hover :
    (∀ (g : LaurentSeries ℚ) (hg : g ∈ modularFunctionFieldFull M')
      (hgi : (⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers),
      (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) →
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) :
          ↥(modularFunctionFieldBar M'))) →
      (R₀.residue ⟨_, hgi⟩ : modularFunctionFieldC (ResidueField A) M') ∈
          (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
      ∀ (hgK : (coeffEmb ↥k₀ g) ∈ Kℓ)
        (hgC : (⟨_, hgK⟩ : ↥Kℓ) ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ),
      ∀ (c : ↥k₀) (hc : (c : (AlgebraicClosure ℚ)) ∈ A),
        residue A ⟨(c : (AlgebraicClosure ℚ)), hc⟩ =
          (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨_, hgi⟩) →
        (⟨⟨_, hgK⟩, hgC⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ)) -
            algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ) ⟨c, hc⟩ ∈ y))
    (hjK : ModularCurve.jqNModC ↥k₀ q ∈ Kℓ)
    (hjC : (⟨ModularCurve.jqNModC ↥k₀ q, hjK⟩ : ↥Kℓ) ∈ chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ)
    (a₀ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) (ha₀y : (⟨(⟨ModularCurve.jqNModC ↥k₀ q, hjK⟩ : ↥Kℓ), hjC⟩ : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ)) - algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ) a₀ ∈ y)
    (ξ : ↥k₀) (hξ : IsPrimitiveRoot ξ q)
    (G : Subgroup (↥Kℓ ≃ₐ[↥k₀] ↥Kℓ)) (hGfin : Finite ↥G)
    (hGatt : ∀ τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, τ ∈ G → ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q ∧ γ ∈ CongruenceSubgroup.Gamma0 M' ∧
      ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ⁻¹ Kℓ τ)
    (K₀ : IntermediateField ↥k₀ ↥Kℓ) (hK₀ : K₀ = IntermediateField.fixedField G)
    (Õ : Subring ↥Kℓ) (O : Subring ↥K₀) (hOdef : O = Õ.comap (algebraMap ↥K₀ ↥Kℓ))
    (Bx : Subalgebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ)
    (hBxG : ∀ σ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, σ ∈ G → ∀ f : ↥Kℓ, f ∈ Bx → σ f ∈ Bx)
    (hRN9 : (∃ b : ↥Kℓ, b ∈ Bx ∧ ∀ V : ValuationSubring ↥Kℓ, (∀ x : ↥k₀, algebraMap ↥k₀ ↥Kℓ x ∈ V ↔ ∃ a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ a = x) →
                (∀ hϖV : algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ ⟨π₀, hπ⟩ ∈ V, (⟨algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ ⟨π₀, hπ⟩, hϖV⟩ : ↥V) ∈ maximalIdeal ↥V) →
                (∀ hjV : (jℓ : ↥Kℓ) ∈ V, (∀ p : Polynomial ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), p.Monic →
                    ∀ hp : Polynomial.aeval (jℓ : ↥Kℓ) (p.map (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ)) ∈ V,
                      (⟨_, hp⟩ : ↥V) ∉ maximalIdeal ↥V) →
                  (∃ f : ↥Kℓ, f ∈ Õ ∧ f ∉ V) → b ∉ V))) :
    (∃ b : ↥K₀, b ∈ Bx.toSubring.comap (algebraMap ↥K₀ ↥Kℓ) ∧ ∀ V : ValuationSubring ↥K₀,
                  (∀ x : ↥k₀, (x : (AlgebraicClosure ℚ)) ∈ A ↔ algebraMap ↥k₀ ↥K₀ x ∈ V) →
                  (∀ hπV : algebraMap ↥k₀ ↥K₀ π₀ ∈ V, (⟨_, hπV⟩ : ↥V) ∈ maximalIdeal ↥V) →
                  ∀ (hjK' : (coeffEmb ↥k₀ jq) ∈ Kℓ) (hjF : (⟨(coeffEmb ↥k₀ jq), hjK'⟩ : ↥Kℓ) ∈ K₀) (hjV : (⟨_, hjF⟩ : ↥K₀) ∈ V),
                    (∀ p : Polynomial ↥k₀, p.Monic → (∀ i : ℕ, ((p.coeff i : ↥k₀) : (AlgebraicClosure ℚ)) ∈ A) →
                      ∀ hp : Polynomial.aeval (⟨_, hjF⟩ : ↥K₀) (p.map (algebraMap ↥k₀ ↥K₀)) ∈ V,
                        (⟨_, hp⟩ : ↥V) ∉ maximalIdeal ↥V) →
                  (∃ f : ↥K₀, f ∈ O ∧ f ∉ V) → b ∉ V) := by sorry
