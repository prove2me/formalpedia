-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_hasValue_of_mem_smoothLocalRingSnd_levelOne
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.exists_hasValue_of_mem_smoothLocalRingSnd_levelOne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/6e4e218a-7246-5a45-b01b-9d186fbb95ea
-- title:
--   Values at strict second-kind places of a level-one model
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, an algebraically closed field $k$ of characteristic $q$ and a ring homomorphism $\mathrm{red} : A \to k$. Let $data$ consist of a monic polynomial $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(q)$ annihilating the pair $(j, j_q)$, let $hKr$ be the Kronecker congruence asserting that the reduction of $\Phi$ modulo $q$ equals $(C X^q - X)(C X - X^q)$, and let $h\alpha$, $h\beta$ assert that the two Hecke maps $\alpha$, $\beta$ from level $1$ to level $q$ over $\overline{\mathbb{Q}}$ are integral ring homomorphisms. Let $P$ be a place specialisation of the level-one data over $(A, k, \mathrm{red})$, let $R$ be a prolongation tuple over $P$, and assume $hR$, i.e. $R$ satisfies the two divisor laws and the cusp laws at $\infty$ and at $0$. Let $W$ be a place of the level-$(1\cdot q)$ field $\overline{\mathbb{Q}}$-field $\mathrm{modularFunctionFieldBar}(1 \cdot q)$ which is strict of the second kind for $P$: the first reduction of $W$ is the geometric Frobenius image of its second reduction $v := P.\mathrm{reduceSnd}\,W$ (obtained by restricting $W$ along $\beta$ and applying $P.\mathrm{sp}$), and $v$ is not fixed by the square of that Frobenius. Let $r$ be an element of the level-$(1 \cdot q)$ field lying in the ring of integers of $R.R_2$, and assume moreover that $r$ lies in the smooth local ring of $R$ at $v$ on the second copy, i.e. $r$ is $R_2$-integral and lies in the valuation subring of every place of $\mathrm{modularFunctionFieldBar}(1\cdot q)$ that is strict of the second kind with second reduction equal to $v$. Then there is $c \in A$ such that $r$ lies in the valuation subring of $W$ with residue the image of $c$ in the residue field of $W$, and simultaneously the second residue $R.\mathrm{residue}_2(r)$, an element of the characteristic-$q$ level-one function field, lies in the valuation subring of $v$ with residue the image of $\mathrm{red}\,c$.
--
--   This is the integrality-and-compatibility statement at a smooth point of the second component of the reduction of $X_0(q)$ in characteristic $q$: a function regular at all strict second-kind places above $v$ takes an $A$-integral value at $W$, and its reduction takes the reduced value at $v$. It is used in the construction of component charts and attached annuli for a model tuple at level one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_hasValue_of_mem_smoothLocalRingSnd_levelOne.lean

import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_ProlongationTupleSmoothPoint

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.exists_hasValue_of_mem_smoothLocalRingSnd_levelOne
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ}
    {R : P.ProlongationTuple} (hR : R.IsModel)
    {W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))} (hW : P.IsStrictSnd W)
    (r : ↥(modularFunctionFieldBar (1 * q))) (h₂ : r ∈ R.R₂.integers)
    (hr : r ∈ R.smoothLocalRingSnd (P.reduceSnd W)) :
    ∃ c : A, W.HasValue r (c : AlgebraicClosure ℚ) ∧
      (P.reduceSnd W).HasValue (R.residue₂ ⟨r, h₂⟩) (red c) := by sorry
