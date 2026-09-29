-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_SemistableCovering_exists_drinfeldClause_of_regularProlongation_of_exists_algEquiv_quotField_hedged
-- name    : ModularCurve.FullLevel.SemistableCovering.exists_drinfeldClause_of_regularProlongation_of_exists_algEquiv_quotField_hedged
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:30.533368+00:00
-- url     : https://prove2.me/theorems/8e6920ca-ac55-54d2-b89a-2089ad5ae63e
-- title:
--   Drinfeld clause from a regular prolongation, hedged exponent
-- statement:
--   Fix a prime $q$, a natural number $M' \neq 0$, a valuation subring $A$ of $\overline{\mathbb Q}$, a finite set $W$ of places of $\mathrm{modularFunctionFieldC}(\kappa, M')$ over the residue field $\kappa = \mathrm{ResidueField}\,A$, a semistable covering $\mathcal C$ of type `SemistableCovering q M' A W`, a place $s \in W$, an element $\pi \in \overline{\mathbb Q}$, and a field $FSS$ that is a $\kappa$-algebra. Let $R$ be a regular prolongation of $A$ to the field $\mathrm{fieldBar}\,q\,M' = \overline{\mathbb Q}\cdot F(\Gamma_H(q^2M'))$ with residue target $FSS$, i.e. a valuation subring $R.\mathrm{integers}$ of that field whose contraction to $\overline{\mathbb Q}$ is $A$, together with a surjection $R.\mathrm{residue}$ onto $FSS$ with kernel the maximal ideal, compatible with $\kappa$ and satisfying the scaling condition. Assume $R.\mathrm{integers}$ coincides with the valuation subring of the chart $\mathcal C.CSS\,s$, and that it is preserved by pullback along $\mathrm{levelAutBar}\,q\,M'\,\zeta\,\gamma$ for all labels $\zeta : \mathrm{Idx}\,q$ and all $\gamma \in \Gamma_0(M')$. Let $n_{C} \in \mathbb N$, and assume the hypothesis `hDL`: for every ring homomorphism $\iota' : \mathbb F_{q^2} \to \kappa$, viewed as making $\kappa$ an $\mathbb F_{q^2}$-algebra, and whenever $\mathrm{CoordRing}\,q\,\kappa$ is a domain, there is a subgroup $C_s \le \mu_{q+1}(\mathbb F_{q^2})$ with $\mathrm{Nat.card}\,C_s = n_C$ such that for each $\zeta$ there are $\eta \in \{1, q\}$ and a $\kappa$-algebra isomorphism $e$ of $FSS$ with the fixed field $\mathrm{quotField}\,q\,\kappa\,C_s$ inside the Drinfeld function field, for which (i) for $\gamma \in \Gamma_0(M')$ with $\mathrm{levelAutBar}\,q\,M'\,\zeta\,\gamma^{-1}$ preserving $R.\mathrm{integers}$ and $(\overline\gamma, 1) \in \mathrm{hSubgroup}\,q$, the residue automorphism $R.\mathrm{resAut}$ of that level automorphism corresponds under $e$ to $\mathrm{hFunctionFieldAction}$ at $(\overline\gamma, 1)$, and (ii) for $\tau$ in the inertia subgroup of $A$ over $\mathbb Q$ and $\alpha \in \mathbb F_{q^2}^{\times}$ with $\iota'(\alpha) = A.\mathrm{tameCharacter}\,\pi\,\tau$, the semilinear automorphism $\mathrm{arithmeticGalois}\,\tau$ preserves $R.\mathrm{integers}$ and every ring automorphism $\varphi$ of $FSS$ compatible with it through $R.\mathrm{residue}$ corresponds under $e$ to $\mathrm{hFunctionFieldAction}$ at $(\mathrm{diagOneElem}\,q\,(d^{\eta})^{-1}, \alpha^{\eta})$, for $d \in (\mathbb Z/q)^{\times}$ with image $\alpha^{q+1}$. Then, for a given $\iota : \mathbb F_{q^2} \to \kappa$ and with $\mathrm{CoordRing}\,q\,\kappa$ a domain, for every $\zeta : \mathrm{Idx}\,q$ there is $\eta \in \{1, q\}$ with $\mathcal C.\mathrm{DrinfeldClause}\,\pi\,\iota\,\eta\,\zeta\,s$: there exist $C \le \mu_{q+1}(\mathbb F_{q^2})$ and a $\kappa$-algebra isomorphism $e$ of $\mathcal C.FSS\,s$ with $\mathrm{quotField}\,q\,\kappa\,C$ such that, for each $\gamma \in \Gamma_0(M')$, some ring automorphism of $\mathcal C.FSS\,s$ is induced on the chart $\mathcal C.CSS\,s$ by $\mathrm{levelAutBar}\,q\,M'\,\zeta\,\gamma^{-1}$ and every such automorphism matches $\mathrm{hFunctionFieldAction}$ at $(\overline\gamma, 1)$ under $e$, and likewise, for each inertia element $\tau$ and each $\alpha$ with $\iota(\alpha)$ the tame character value, some ring automorphism is induced by $\mathrm{arithmeticGalois}\,\tau$ and every such one matches $\mathrm{hFunctionFieldAction}$ at $(\mathrm{diagOneElem}\,q\,(d^{\eta})^{-1}, \alpha^{\eta})$.
--
--   This is the transport step that converts a Drinfeld identification carried by a regular prolongation of $A$ to the modular function field into the corresponding clause for the supersingular chart of the semistable covering, the exponent $\eta \in \{1, q\}$ being left hedged label by label. It is used by the results identifying the supersingular components of the reduction at $q$ for valuation subrings over the fixed field in the cases $q = 2$ and $q = 3$, which in turn feed the description of the reduction of $X_H(q^2M')$ used in the level-lowering argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_SemistableCovering_exists_drinfeldClause_of_regularProlongation_of_exists_algEquiv_quotField_hedged.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCoveringNaturality
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringGuards
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringW2
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_ModularCurve_ArithmeticGalois

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

theorem ModularCurve.FullLevel.SemistableCovering.exists_drinfeldClause_of_regularProlongation_of_exists_algEquiv_quotField_hedged
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M']
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (𝒞 : SemistableCovering q M' A W) (s : ↥W)
    (π : AlgebraicClosure ℚ)
    {FSS : Type} [Field FSS] [Algebra (ResidueField A) FSS]
    (R : RegularProlongation A (fieldBar q M') FSS)
    (hR : R.integers = (𝒞.CSS s).integers)
    (hfix : ∀ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
      R.integers.comap (levelAutBar q M' ζ γ).toAlgHom.toRingHom = R.integers)
    {nCs : ℕ}
    (hDL : (∀ (ι : GaloisField q 2 →+* ResidueField ↥A),
            letI : Algebra (GaloisField q 2) (ResidueField ↥A) := ι.toAlgebra
            ∀ (_ : IsDomain (DrinfeldCurve.CoordRing q (ResidueField ↥A))),
            ∃ (Cs : Subgroup (rootsOfUnity (q + 1) (GaloisField q 2))),
              Nat.card Cs = nCs ∧
              ∀ (ζ : Idx q), ∃ η : ℕ, (η = 1 ∨ η = q) ∧ ∃ (e : FSS ≃ₐ[ResidueField ↥A] ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)),
                (∀ (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
                  ∀ (hτ : ∀ f : ↥(fieldBar q M'), levelAutBar q M' ζ γ⁻¹ f ∈ R.integers ↔ f ∈ R.integers)
                    (hmem : (redQ q γ, (1 : (GaloisField q 2)ˣ)) ∈ DrinfeldCurve.hSubgroup q),
                    ∀ x : FSS,
                      ((e (R.resAut (levelAutBar q M' ζ γ⁻¹) hτ x) : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)) : DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) =
                        DrinfeldCurve.hFunctionFieldAction q (ResidueField ↥A) ⟨_, hmem⟩ ((e x : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)) : DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A))) ∧
                (∀ τ ∈ A.inertiaSubgroupIn ℚ, ∀ α : (GaloisField q 2)ˣ,
                  ι (α : GaloisField q 2) = A.tameCharacter π τ →
                  ∀ (g : SemilinearAut (AlgebraicClosure ℚ) ↥(fieldBar q M')),
                    g = ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ →
                  (∀ f : ↥(fieldBar q M'), g • f ∈ R.integers ↔ f ∈ R.integers) ∧
                  ∀ (hst : ∀ f : ↥(fieldBar q M'), g • f ∈ R.integers ↔ f ∈ R.integers)
                    (φ : FSS ≃+* FSS),
                    (∀ (f : ↥(fieldBar q M')) (hf : f ∈ R.integers),
                      R.residue ⟨g • f, (hst f).mpr hf⟩ = φ (R.residue ⟨f, hf⟩)) →
                    ∀ (d : (ZMod q)ˣ), algebraMap (ZMod q) (GaloisField q 2) (d : ZMod q) = (α : GaloisField q 2) ^ (q + 1) →
                      ∀ (hmem : (diagOneElem q (d ^ η)⁻¹, α ^ η) ∈ DrinfeldCurve.hSubgroup q),
                        ∀ x : FSS,
                          ((e (φ x) : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)) : DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) =
                            DrinfeldCurve.hFunctionFieldAction q (ResidueField ↥A) ⟨_, hmem⟩ ((e x : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)) : DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)))))
    (ι : GaloisField q 2 →+* ResidueField A)
    [IsDomain (DrinfeldCurve.CoordRing q (ResidueField A))] :
    letI : Algebra (GaloisField q 2) (ResidueField A) := ι.toAlgebra
    ∀ ζ : Idx q, ∃ η : ℕ, (η = 1 ∨ η = q) ∧ 𝒞.DrinfeldClause π ι η ζ s := by sorry
