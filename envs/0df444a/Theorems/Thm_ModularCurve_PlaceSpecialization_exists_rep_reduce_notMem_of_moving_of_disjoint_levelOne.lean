-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_exists_rep_reduce_notMem_of_moving_of_disjoint_levelOne
-- name    : ModularCurve.PlaceSpecialization.exists_rep_reduce_notMem_of_moving_of_disjoint_levelOne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/ee9479c7-4717-5396-9838-cc66ea65508d
-- title:
--   Moving lemma for degree-zero classes at level 1· q
-- statement:
--   Let $q$ be a prime and let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ lying over $q$, in the sense that the image of $q$ lies in the nonunits of $A$; then the residue field $k = \mathrm{ResidueField}(A)$ has characteristic $q$. Let $W$ be a finite set of places of $\mathrm{modularFunctionFieldC}(k,1)$ over $k$ whose members are exactly the supersingular places $\mathrm{ssPlaces}\,q\,1\,k$ (rational affine geometric places whose value at the geometric $j$-generator lies in $\mathrm{ssJSet}\,q\,k$). Let `data` be modular polynomial data for $q$ satisfying the Kronecker congruence, let the two degeneracy embeddings $\mathrm{heckeAlphaBar}$ and $\mathrm{heckeBetaBar}$ from level $1$ to level $1\cdot q$ over $\overline{\mathbb{Q}}$ be integral, and let $P$ be a `PlaceSpecialization` for $A$, $q$, level $1$, these data and the residue map $A \to k$. Assume further that for every finite set $T$ of places of $\mathrm{modularFunctionFieldC}(k,1)$ there are divisors $E_0, C_0$ on $\mathrm{modularFunctionFieldBar}(1\cdot q)$ over $\overline{\mathbb{Q}}$ with: $E_0$ effective of positive degree; every place in the support of $E_0$ strict for $P$ in the first or the second sense ($P.\mathrm{IsGoodDiv}$) and having both reductions $P.\mathrm{reduceFst}$, $P.\mathrm{reduceSnd}$ outside $T$; $C_0$ effective of positive degree and fixed by the arithmetic Galois action of every element of the inertia subgroup of $A$ over $\mathbb{Q}$; and $E_0 - C_0$ principal. The conclusion: for every finite set $T$ of places of $\mathrm{modularFunctionFieldC}(k,1)$ disjoint from $W$ and every class $x \in \mathrm{JZero}(1\cdot q) = \mathrm{Pic}^0(\overline{\mathbb{Q}}, \mathrm{modularFunctionFieldBar}(1\cdot q))$, there is a degree-zero divisor $E$ with $\mathrm{Pic0.mk}\,E = x$ such that every place in the support of $E$ has both reductions $P.\mathrm{reduceFst}$ and $P.\mathrm{reduceSnd}$ outside $T$.
--
--   This is the moving lemma for the Jacobian at level $1 \cdot q$: every degree-zero divisor class admits a representative whose places reduce, under both degeneracy maps, away from a prescribed finite set of places of the characteristic-$q$ fibre, provided that set avoids the supersingular locus. It is the level-one case of the general moving statement and is used in the construction of good representatives for classes of the form $x - \sigma \cdot x$ entering the analysis of the action of inertia on $J_0(q)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_exists_rep_reduce_notMem_of_moving_of_disjoint_levelOne.lean

import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_WeierstrassCurve_ReductionMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option Elab.async false
open AlgebraicCurve IsLocalRing ModularCurve
set_option autoImplicit false

theorem ModularCurve.PlaceSpecialization.exists_rep_reduce_notMem_of_moving_of_disjoint_levelOne
    (q : ℕ) (hq : q.Prime)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    haveI : Fact q.Prime := ⟨hq⟩
    haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A 1
    ∀ (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) 1)))
      (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q 1 (ResidueField A))
      (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)
      (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q)
      (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q)
      (P : PlaceSpecialization A q 1 data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ),
        (∀ T : Finset (Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) 1)),
          ∃ E₀ C₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)),
            (∀ V, 0 ≤ E₀ V) ∧ P.IsGoodDiv E₀ ∧
              (∀ V ∈ E₀.support, P.reduceFst V ∉ T ∧ P.reduceSnd V ∉ T) ∧
                0 < Divisor.degree E₀ ∧ (∀ V, 0 ≤ C₀ V) ∧
                  (∀ σ ∈ A.inertiaSubgroupIn ℚ,
                    arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • C₀ = C₀) ∧
                    0 < Divisor.degree C₀ ∧ Divisor.IsPrincipal (E₀ - C₀)) →
          ∀ (T : Finset (Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) 1))),
          (∀ w ∈ T, w ∉ W) →
          ∀ x : JZero (1 * q),
            ∃ (E : ↥(Divisor.degZero (K := AlgebraicClosure ℚ)
                  (F := ↥(modularFunctionFieldBar (1 * q))))),
              Pic0.mk E = x ∧
                ∀ V ∈ (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))).support,
                  P.reduceFst V ∉ T ∧ P.reduceSnd V ∉ T := by sorry
