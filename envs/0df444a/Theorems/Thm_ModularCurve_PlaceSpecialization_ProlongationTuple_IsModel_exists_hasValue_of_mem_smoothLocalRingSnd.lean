-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_hasValue_of_mem_smoothLocalRingSnd
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.exists_hasValue_of_mem_smoothLocalRingSnd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/df6ba93c-bc1a-5924-bc1e-e746a8e58a28
-- title:
--   Value law at smooth points of the second prolongation
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, a positive integer $N$, an algebraically closed field $k$ of characteristic $q$ and a ring homomorphism $\mathrm{red} : A \to k$; fix data $\mathrm{data}$ consisting of a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(q)$ with $\Phi$ vanishing on the relevant $q$-expansions, a witness $h_{Kr}$ that $\Phi$ reduces mod $q$ to $(C(X)^q - X)(C(X) - X^q)$, and witnesses $h_\alpha$, $h_\beta$ that the two Hecke maps at $q$ in level $N$ are integral ring homomorphisms; fix a place specialisation $P$ for these data. Assume $q \nmid N$, let $R$ be a prolongation tuple for $P$ satisfying the model laws (the two divisor laws and the two cusp laws), and let $W$ be a place of $\overline{\mathbb{Q}}$-valued modular function field of level $Nq$ which is strict of the second kind, i.e. $P.\mathrm{reduceFst}\,W$ is the Frobenius image of $u := P.\mathrm{reduceSnd}\,W$ and the second Frobenius iterate of $u$ differs from $u$. Let $r$ be an element of that function field which is $R_2$-integral, with witness $h_2$, and which lies in the subring $R.\mathrm{smoothLocalRingSnd}\,u$, that is: $r$ is $R_2$-integral and lies in the valuation ring of every place of the level-$Nq$ field that is strict of the second kind with second reduction $u$. Then there exists $c \in A$ such that $r$ lies in the valuation ring of $W$ with residue the image of $c$, and the reduction `R.residue₂ ⟨r, h₂⟩` of $r$ attached to the second prolongation lies in the valuation ring of $u$ with residue the image of $\mathrm{red}\,c$.
--
--   This is the value law for the second copy: a function with no pole in the residue discs of the second kind above a point $u$ takes at every such place a value in $A$, and its reduction takes the reduced value at $u$. It is used in the construction of component charts and of attached annuli for the model of $X_0(Nq)$ in characteristic $q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_hasValue_of_mem_smoothLocalRingSnd.lean

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

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.exists_hasValue_of_mem_smoothLocalRingSnd
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (hqN : ¬ q ∣ N) {R : P.ProlongationTuple} (hR : R.IsModel)
    {W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))} (hW : P.IsStrictSnd W)
    (r : ↥(modularFunctionFieldBar (N * q))) (h₂ : r ∈ R.R₂.integers)
    (hr : r ∈ R.smoothLocalRingSnd (P.reduceSnd W)) :
    ∃ c : A, W.HasValue r (c : AlgebraicClosure ℚ) ∧
      (P.reduceSnd W).HasValue (R.residue₂ ⟨r, h₂⟩) (red c) := by sorry
