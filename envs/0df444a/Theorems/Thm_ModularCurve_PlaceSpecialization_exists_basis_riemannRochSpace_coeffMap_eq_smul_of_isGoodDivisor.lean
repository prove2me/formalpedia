-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_exists_basis_riemannRochSpace_coeffMap_eq_smul_of_isGoodDivisor
-- name    : ModularCurve.PlaceSpecialization.exists_basis_riemannRochSpace_coeffMap_eq_smul_of_isGoodDivisor
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/e33f0a21-9ebb-5005-a34f-77f333552199
-- title:
--   Gauss-normalisable basis of L(D) for a good divisor
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a field $k$ of characteristic $q$ and a ring homomorphism $red : A \to k$. Fix furthermore modular polynomial data `data` for $q$ (a monic $\Phi \in \mathbb Z[X][Y]$ of degree $\psi(q)$ annihilating the pair $(j, j_q)$), a proof `hKr` that its bivariate reduction modulo $q$ equals $(X^q - Y)(X - Y^q)$ in the relevant indeterminates, and proofs `hα`, `hβ` that the ring homomorphisms underlying the Hecke maps $\bar\alpha$, $\bar\beta$ at level $1$ and prime $q$ are integral. Let $P$ be a place specialisation datum of type `PlaceSpecialization A q 1 data hKr k red hα hβ`, and let $D$ be a divisor on the field $F = \overline{\mathbb Q}\,$-base change of the full modular function field of level $1 \cdot q$, viewed inside $\overline{\mathbb Q}((\mathfrak q))$, that is, a finitely supported $\mathbb Z$-valued function on the places of $F$ over $\overline{\mathbb Q}$. Assume $D$ is good for $P$: every place in the support of $D$ satisfies `P.IsStrictTypeOne` or `P.IsStrictTypeTwo`. Assume the Riemann–Roch space $L(D) = \{f \in F : v(f) \le \exp(D v) \text{ for all places } v\}$ is finite-dimensional over $\overline{\mathbb Q}$, of dimension $n$. Then there is a family $b : \mathrm{Fin}\,n \to F$ with all $b_i \in L(D)$, linearly independent over $\overline{\mathbb Q}$ (hence a basis of $L(D)$), such that for each $i$ there are nonzero scalars $c, c' \in \overline{\mathbb Q}$ with $c \cdot b_i$ and $c' \cdot \overline{w_q}(b_i)$ lying in the image of `coeffMap A.subtype`, i.e. both the $\mathfrak q$-expansion of $c\,b_i$ and that of $c'$ times the Fricke transform `frickeInvolutionBar (1 * q) (b i)` have all coefficients in $A$.
--
--   This is the bounded-denominators (Gauss normalisation) step for $\mathfrak q$-expansions on $X_0(q)$: for a divisor all of whose support is of strict type, the members of $L(D)$ and their Fricke transforms can be rescaled to have $A$-integral expansions at the cusp. It is used by the level-one prolongation lemmas producing elements of $L(D)$ with prescribed residues, and with prescribed behaviour under inertia.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_exists_basis_riemannRochSpace_coeffMap_eq_smul_of_isGoodDivisor.lean

import Mathlib
import Definitions.Def_ModularCurve_LevelOneProlongationPair
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve ModularCurve ModularCurve.PlaceSpecialization

theorem ModularCurve.PlaceSpecialization.exists_basis_riemannRochSpace_coeffMap_eq_smul_of_isGoodDivisor
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q]
    {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) (hgood : P.IsGoodDivisor D)
    [FiniteDimensional (AlgebraicClosure ℚ) (riemannRochSpace D)] :
    ∃ b : Fin (Module.finrank (AlgebraicClosure ℚ) (riemannRochSpace D)) → modularFunctionFieldBar (1 * q),
      (∀ i, b i ∈ riemannRochSpace D) ∧ LinearIndependent (AlgebraicClosure ℚ) b ∧
      ∀ i, (∃ (c : AlgebraicClosure ℚ) (y : LaurentSeries A), c ≠ 0 ∧
              coeffMap A.subtype y = c • ((b i : modularFunctionFieldBar (1 * q)) :
                LaurentSeries (AlgebraicClosure ℚ))) ∧
           (∃ (c : AlgebraicClosure ℚ) (y : LaurentSeries A), c ≠ 0 ∧
              coeffMap A.subtype y = c • ((frickeInvolutionBar (1 * q) (b i) :
                modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ))) := by sorry
