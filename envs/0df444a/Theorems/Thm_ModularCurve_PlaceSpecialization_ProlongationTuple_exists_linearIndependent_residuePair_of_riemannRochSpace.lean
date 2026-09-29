-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_linearIndependent_residuePair_of_riemannRochSpace
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.exists_linearIndependent_residuePair_of_riemannRochSpace
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/a4bf2c20-e076-5ac0-9906-f427acbb2b00
-- title:
--   Bi-integral basis of a Riemann–Roch space with independent residue pairs
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, an integer $N \ge 1$, a field $k$ of characteristic $q$ and a ring homomorphism $red : A \to k$; fix data `data` for the modular polynomial at $q$ (a monic $\Phi \in \mathbb Z[X][Y]$ of degree $\psi(q)$ annihilating the pair $(j, j_q)$) together with the Kronecker congruence `hKr`, asserting that the bivariate reduction of $\Phi$ modulo $q$ equals $(Y^q - X)(Y - X^q)$, and the hypotheses $h\alpha$, $h\beta$ that the two degeneracy (Hecke) homomorphisms $\overline{\alpha}$, $\overline{\beta}$ at level $N$ and prime $q$ over $\overline{\mathbb Q}$ are integral ring maps. Let $P$ be a `PlaceSpecialization` for these data, let $R$ be a `ProlongationTuple` for $P$, with its two regular prolongations $R.R_1$, $R.R_2$ of $A$ to the function field $\overline{\mathbb Q}(X_0(Nq))$ with residue fields mapped into $k(X_0(N)) =$ `modularFunctionFieldC k N`, and assume $q \nmid N$. Let $E$ be a divisor on $\overline{\mathbb Q}(X_0(Nq))$, that is, a finitely supported $\mathbb Z$-valued function on its places, whose Riemann–Roch space $L(E) = \{f : v(f) \le \exp(E(v)) \text{ for all places } v\}$ is finite-dimensional over $\overline{\mathbb Q}$, of dimension $n$. Then there exist $G_1, \dots, G_n$ in $\overline{\mathbb Q}(X_0(Nq))$, each lying in the valuation ring $R.R_1$`.integers` and in $R.R_2$`.integers` and each lying in $L(E)$, such that the family of residue pairs $(R$`.residue₁`$(G_i), R$`.residue₂`$(G_i)) \in k(X_0(N)) \times k(X_0(N))$, $i = 1, \dots, n$, is linearly independent over $k$. No sign condition is imposed on $E$.
--
--   This is the Gauss-type normalisation of a Riemann–Roch space simultaneously with respect to both prolongations attached to a place specialisation of $X_0(Nq)$ at $q$: a full-dimensional family of sections of $L(E)$ that is integral on both sides and whose reductions remain independent over the residue field. It is used in the construction of models, namely by [`ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.exists_mem_riemannRochSpace_residue_eq_of_isGoodDiv`](thm.html#ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.exists_mem_riemannRochSpace_residue_eq_of_isGoodDiv), to realise prescribed residues by sections with controlled poles.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_linearIndependent_residuePair_of_riemannRochSpace.lean

import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve.PlaceSpecialization
open ModularCurve

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.exists_linearIndependent_residuePair_of_riemannRochSpace
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P) (hqN : ¬ q ∣ N)
    (E : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    [FiniteDimensional (AlgebraicClosure ℚ) ↥(riemannRochSpace E)] :
    ∃ (G : Fin (Module.finrank (AlgebraicClosure ℚ) ↥(riemannRochSpace E)) → ↥(modularFunctionFieldBar (N * q)))
      (hG₁ : ∀ i, G i ∈ R.R₁.integers) (hG₂ : ∀ i, G i ∈ R.R₂.integers),
      (∀ i, G i ∈ riemannRochSpace E) ∧
      LinearIndependent k (fun i =>
        ((R.residue₁ ⟨G i, hG₁ i⟩ : ↥(modularFunctionFieldC k N)), (R.residue₂ ⟨G i, hG₂ i⟩ : ↥(modularFunctionFieldC k N)))) := by sorry
