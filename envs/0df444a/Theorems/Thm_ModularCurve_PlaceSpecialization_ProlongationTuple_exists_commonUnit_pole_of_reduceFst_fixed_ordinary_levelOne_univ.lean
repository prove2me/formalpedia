-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_commonUnit_pole_of_reduceFst_fixed_ordinary_levelOne_univ
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.exists_commonUnit_pole_of_reduceFst_fixed_ordinary_levelOne_univ
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/2e6bc2c7-cf3e-5b57-8a3a-b53a1d28e285
-- title:
--   Common unit with a simple pole at an ordinary fixed place
-- statement:
--   Let $q$ be a prime, $A$ a valuation subring of $\overline{\mathbb Q}$, $k$ an algebraically closed field of characteristic $q$ and $\mathrm{red}\colon A\to k$ a ring homomorphism. Let `data` consist of a monic $\Phi\in\mathbb Z[X][Y]$ of degree $\psi(q)$ annihilating $(j,j_q)$, with `hKr` asserting the Kronecker congruence $\Phi\equiv (C X^{q}-X)(C X-X^{q})$ modulo $q$, and let `hα`, `hβ` say that the two degeneracy embeddings `heckeAlphaBar`, `heckeBetaBar` from level $1$ into level $1\cdot q$ over $\overline{\mathbb Q}$ are integral. Let $P$ be a `PlaceSpecialization` of these data and $R$ a `ProlongationTuple` for $P$, satisfying `IsModel` (the two divisor laws and the two cusp laws) and `OrderLawFixed`. Let $V_0$ be a place of $\mathrm{modularFunctionFieldBar}(1\cdot q)$ over $\overline{\mathbb Q}$ such that $v:=P.\mathrm{reduceFst}\,V_0$ is fixed by the square of the Frobenius operation `frobOnPlacesGeomLevel` on places of $\mathrm{modularFunctionFieldC}\,k\,1$, satisfies `IsAffineGeomPlace` (both $\tilde\jmath=$`jGeomGen` and `jNGeomGen` lie in its valuation subring) and does not lie in `ssPlaces q 1 k`. Then for every finite $S\subseteq k$ and every finite set $B$ of places of $\mathrm{modularFunctionFieldC}\,k\,1$ there is $g\in\mathrm{modularFunctionFieldBar}(1\cdot q)$ lying in the valuation subrings $R.R_1.\mathrm{integers}$ and $R.R_2.\mathrm{integers}$, with both residues $R.R_1.\mathrm{residue}\,g$ and $R.R_2.\mathrm{residue}\,g$ nonzero, such that $\mathrm{ord}_{V_0}g=-1$; every place $V\neq V_0$ with $\mathrm{ord}_V g<0$ satisfies $\mathrm{ord}_V(\mathrm{jFun}\,1\,q-a)>0$ for some $a\in A$ with $\mathrm{red}\,a\notin S$, and both $P.\mathrm{reduceFst}\,V$ and $P.\mathrm{reduceSnd}\,V$ avoid $B$; and finally either $\mathrm{ord}_v(R.\mathrm{residue}_1 g)=-1$ and $\mathrm{ord}_{\varphi v}(R.\mathrm{residue}_2 g)=0$, or $\mathrm{ord}_v(R.\mathrm{residue}_1 g)=0$ and $\mathrm{ord}_{\varphi v}(R.\mathrm{residue}_2 g)=-1$, where $\varphi$ denotes `frobOnPlacesGeomLevel k 1 data hKr`.
--
--   This is the level-one ($N=1$) form of the construction of a function on $X_0(q)$ over $\overline{\mathbb Q}$ with a prescribed simple pole, whose remaining poles avoid prescribed $j$-values and prescribed places of the special fibre, and whose two reductions split the pole between the two components of the special fibre over an ordinary point fixed by the square of Frobenius. It feeds the first-sheet divisor law at level one and the corresponding statement over a general residue field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_commonUnit_pole_of_reduceFst_fixed_ordinary_levelOne_univ.lean

import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_SupersingularNodePlaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option Elab.async false
set_option autoImplicit false
open AlgebraicCurve ModularCurve ModularCurve.PlaceSpecialization.ProlongationTuple
open ModularCurve.PlaceSpecialization hiding jFun

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.exists_commonUnit_pole_of_reduceFst_fixed_ordinary_levelOne_univ
    (q : ℕ) [Fact q.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
    (k : Type*) [Field k] [CharP k q] [DecidableEq k] [IsAlgClosed k] (red : A →+* k)
    (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)
    (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q) (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q)
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (R : ProlongationTuple P) (hR : R.IsModel) (hO : R.OrderLawFixed)
    (V₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))
    (hfix : frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr (P.reduceFst V₀))
      = P.reduceFst V₀)
    (haff : IsAffineGeomPlace k 1 (P.reduceFst V₀)) (hord : P.reduceFst V₀ ∉ ssPlaces q 1 k)
    (S : Finset k) (B : Finset (Place k (modularFunctionFieldC k 1))) :
    ∃ (g : modularFunctionFieldBar (1 * q)) (h₁ : g ∈ R.R₁.integers) (h₂ : g ∈ R.R₂.integers),
      R.R₁.residue ⟨g, h₁⟩ ≠ 0 ∧ R.R₂.residue ⟨g, h₂⟩ ≠ 0 ∧ V₀.ord g = -1 ∧
      (∀ V, V ≠ V₀ → V.ord g < 0 →
        (∃ a : A, 0 < V.ord (jFun 1 q - algebraMap (AlgebraicClosure ℚ)
            (modularFunctionFieldBar (1 * q)) (a : AlgebraicClosure ℚ)) ∧ red a ∉ S) ∧
          P.reduceFst V ∉ B ∧ P.reduceSnd V ∉ B) ∧
      (((P.reduceFst V₀).ord (R.residue₁ ⟨g, h₁⟩) = -1 ∧
          (frobOnPlacesGeomLevel k 1 data hKr (P.reduceFst V₀)).ord (R.residue₂ ⟨g, h₂⟩) = 0) ∨
        ((P.reduceFst V₀).ord (R.residue₁ ⟨g, h₁⟩) = 0 ∧
          (frobOnPlacesGeomLevel k 1 data hKr (P.reduceFst V₀)).ord (R.residue₂ ⟨g, h₂⟩) = -1)) := by sorry
