-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_SemistableCovering_drinfeldClause_of_regularProlongation_of_exists_algEquiv_quotField
-- name    : ModularCurve.FullLevel.SemistableCovering.drinfeldClause_of_regularProlongation_of_exists_algEquiv_quotField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:30.533368+00:00
-- url     : https://prove2.me/theorems/73fdfaab-50a0-599f-b6eb-8df5280d1eda
-- title:
--   Drinfeld clause from a regular prolongation on a supersingular chart
-- statement:
--   Fix a prime $q$, a nonzero $M'$, a valuation subring $A$ of $\overline{\mathbb Q}$ with residue field $\kappa$, a finite set $W$ of places of `modularFunctionFieldC κ M'` over $\kappa$, a `SemistableCovering q M' A W` datum $\mathcal C$, an element $s\in W$, an element $\pi\in\overline{\mathbb Q}$, a field `FSS` that is a $\kappa$-algebra, and a regular prolongation $R$ of $A$ to `fieldBar q M'` with residue map onto `FSS` (a valuation subring `R.integers` over $A$ together with a surjection onto `FSS` whose kernel is the maximal ideal). Assume: `R.integers` coincides with the valuation subring of the chart $\mathcal C.\mathrm{CSS}\,s$; `R.integers` is preserved by pullback along `levelAutBar q M' ζ γ` for every index $\zeta$ and every $\gamma\in\Gamma_0(M')$; and the hypothesis `hDL`, which says that for every ring homomorphism $\mathbb F_{q^2}\to\kappa$, used as the algebra structure, and every witness that [`DrinfeldCurve.CoordRing q κ`](def/DrinfeldCurve_CoordRing.html#L21) is a domain, there is a subgroup $C_s$ of $\mu_{q+1}(\mathbb F_{q^2})$ with $\#C_s = 2\cdot$`placeWidthChar q M' s` and, for each $\zeta$, a $\kappa$-algebra isomorphism $e$ from `FSS` onto the fixed field [`DrinfeldCurve.quotField q κ Cs`](def/ModularCurve_FullLevelSemistableCoveringW2.html#L32) inside the Drinfeld function field such that (i) for $\gamma\in\Gamma_0(M')$ whose level automorphism at $\zeta$ stabilises `R.integers`, the induced residue automorphism `R.resAut` corresponds under $e$ to the action of $(\gamma \bmod q, 1)$ through `hFunctionFieldAction`, and (ii) for $\tau$ in the inertia subgroup of $A$ over $\mathbb Q$ and $\alpha\in\mathbb F_{q^2}^\times$ mapping to `A.tameCharacter π τ`, the arithmetic Galois semilinear automorphism attached to $\tau$ stabilises `R.integers`, and any ring automorphism $\varphi$ of `FSS` compatible with it corresponds under $e$ to the action of $(\mathrm{diag}(1,(d^q)^{-1}), \alpha^q)$ whenever $d\in(\mathbb Z/q)^\times$ maps to $\alpha^{q+1}$. Then, for the given $\iota:\mathbb F_{q^2}\to\kappa$ and every index $\zeta$, the predicate $\mathcal C.\mathrm{DrinfeldClause}\,\pi\,\iota\,q\,\zeta\,s$ holds: there are a subgroup $C$ of $\mu_{q+1}(\mathbb F_{q^2})$ and a $\kappa$-algebra isomorphism from $\mathcal C.\mathrm{FSS}\,s$ onto [`DrinfeldCurve.quotField q κ C`](def/ModularCurve_FullLevelSemistableCoveringW2.html#L32) intertwining, for each $\gamma\in\Gamma_0(M')$, any automorphism induced on the chart $\mathcal C.\mathrm{CSS}\,s$ by the level automorphism of $\gamma^{-1}$ at $\zeta$ with the action of $(\gamma \bmod q,1)$, and, for each inertia element $\tau$ with tame value $\iota(\alpha)$, any automorphism induced on that chart by the arithmetic Galois action of $\tau$ with the action of $(\mathrm{diag}(1,(d^{q})^{-1}),\alpha^{q})$, existence of such induced automorphisms being part of the clause.
--
--   This is the transport step which carries the Drinfeld identification of the residue field of a regular prolongation, together with its equivariance for the level automorphisms and for tame inertia, over to the supersingular chart of a semistable covering, where the exponent in the inertia formula is specialised to $\eta = q$. It is used by [`ModularCurve.FullLevel.SemistableCovering.drinfeldClause_of_valuationSubring_over_fixed`](thm.html#ModularCurve.FullLevel.SemistableCovering.drinfeldClause_of_valuationSubring_over_fixed) in the analysis of the supersingular components of the special fibre of the modular curve of level $q^2M'$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_SemistableCovering_drinfeldClause_of_regularProlongation_of_exists_algEquiv_quotField.lean

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

theorem ModularCurve.FullLevel.SemistableCovering.drinfeldClause_of_regularProlongation_of_exists_algEquiv_quotField
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
    (hDL : (∀ (ι : GaloisField q 2 →+* ResidueField ↥A),
            letI : Algebra (GaloisField q 2) (ResidueField ↥A) := ι.toAlgebra
            ∀ (_ : IsDomain (DrinfeldCurve.CoordRing q (ResidueField ↥A))),
            ∃ (Cs : Subgroup (rootsOfUnity (q + 1) (GaloisField q 2))),
              Nat.card Cs = 2 * placeWidthChar q M' (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')) ∧
              ∀ (ζ : Idx q), ∃ (e : FSS ≃ₐ[ResidueField ↥A] ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)),
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
                      ∀ (hmem : (diagOneElem q (d ^ q)⁻¹, α ^ q) ∈ DrinfeldCurve.hSubgroup q),
                        ∀ x : FSS,
                          ((e (φ x) : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)) : DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) =
                            DrinfeldCurve.hFunctionFieldAction q (ResidueField ↥A) ⟨_, hmem⟩ ((e x : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)) : DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)))))
    (ι : GaloisField q 2 →+* ResidueField A)
    [IsDomain (DrinfeldCurve.CoordRing q (ResidueField A))] :
    letI : Algebra (GaloisField q 2) (ResidueField A) := ι.toAlgebra
    ∀ ζ : Idx q, 𝒞.DrinfeldClause π ι q ζ s := by sorry
