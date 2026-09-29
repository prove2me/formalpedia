-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_IsModel_exists_ringHom_tExpansion
-- name    : ModularCurve.PlaceSpecialization.LevelOneProlongationPair.IsModel.exists_ringHom_tExpansion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/353a43bb-3d0b-5b23-9886-eac66292537e
-- title:
--   Ring homomorphism given by t-expansion at a smooth point
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a field $k$ of characteristic $q$ and a ring homomorphism $\mathrm{red} : A \to k$; let `data` consist of a monic $\Phi \in \mathbb Z[X][Y]$ of degree $\psi(q)$ vanishing on the pair of $q$-expansions of $j$, let `hKr` assert the Kronecker congruence that the bivariate reduction of $\Phi$ modulo $q$ equals $(C(X)^q - X)(C(X) - X^q)$, and let `hα`, `hβ` assert that the two Hecke maps $\bar\alpha$, $\bar\beta$ at level $1$ and prime $q$ are integral ring homomorphisms. Let $P$ be a place specialisation for these data and $R$ one of its level-one prolongation pairs, assumed to satisfy `IsModel`, i.e. the two divisor laws together with the cusp laws at $\infty$ and at $0$. Let $Q$ be a place of $\overline{\mathbb Q}$-modular function field $\overline{\mathcal F}_{1\cdot q}$ of strict type one for $P$ (Frobenius on geometric-level places carries $P.\mathrm{redFst}\,Q$ to $P.\mathrm{redSnd}\,Q$, and its square does not fix $P.\mathrm{redFst}\,Q$), and let $j_0 \in A$ be such that the uniformiser candidate $t := \mathrm{jFun} - j_0$ has $\mathrm{ord}_Q(t) > 0$, where $\mathrm{ord}$ is minus the logarithm of the adic valuation. Write $\mathcal O$ for the subring `R.smoothLocalRingFst (P.redFst Q)` of $\overline{\mathcal F}_{1\cdot q}$, namely the intersection of the integers of $R.R_1$ with the valuation subrings of all strict-type-one places $W$ with $P.\mathrm{redFst}\,W = P.\mathrm{redFst}\,Q$. Then there is a ring homomorphism $\varphi : \mathcal O \to A[[X]]$ such that: (i) for every $r \in \mathcal O$ and every $m \in \mathbb N$, the element $\bigl(r - \sum_{i < m} \mathrm{coeff}_i(\varphi\, r)\, t^i\bigr)/t^m$ again lies in $\mathcal O$, the coefficients being viewed in $\overline{\mathbb Q}$ and mapped into the function field; (ii) if $t$ itself lies in $\mathcal O$ then $\varphi(t) = X$; and (iii) for $a \in A$ whose image lies in $\mathcal O$, $\varphi$ sends it to the constant power series $C(a)$.
--
--   This packages the $t$-adic expansion at a smooth point of the level-$q$ model, with $t = j - j_0$ a uniformiser at a strict-type-one place, into a single ring homomorphism from the semilocal ring $\mathcal O$ to $A[[X]]$ normalised on $t$ and on constants; no completion of $\mathcal O$ is involved, only the remainder condition (i). It is used to transport multiplicative identities in $\mathcal O$ to power series over $A$, and is cited in the estimate `neg_one_le_ord_residue_of_eq_one_add_mul`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_IsModel_exists_ringHom_tExpansion.lean

import Mathlib
import Definitions.Def_ModularCurve_SmoothPointLocalRing

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve IsLocalRing ModularCurve

theorem ModularCurve.PlaceSpecialization.LevelOneProlongationPair.IsModel.exists_ringHom_tExpansion
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ}
    {R : P.LevelOneProlongationPair} (hR : R.IsModel)
    {Q : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))} (hQ : P.IsStrictTypeOne Q)
    (j₀ : A) (hj₀ : 0 < Q.ord (PlaceSpecialization.jFun (q := q) -
          algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (j₀ : AlgebraicClosure ℚ))) :
    ∃ φ : ↥(R.smoothLocalRingFst (P.redFst Q)) →+* PowerSeries ↥A,
      (∀ (r : ↥(R.smoothLocalRingFst (P.redFst Q))) (m : ℕ),
        ((r : ↥(modularFunctionFieldBar (1 * q))) - ∑ i ∈ Finset.range m,
            algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))
              ((PowerSeries.coeff (R := ↥A) i (φ r) : A) : AlgebraicClosure ℚ) *
              (PlaceSpecialization.jFun (q := q) -
          algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (j₀ : AlgebraicClosure ℚ)) ^ i) /
          (PlaceSpecialization.jFun (q := q) -
          algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (j₀ : AlgebraicClosure ℚ)) ^ m ∈
        R.smoothLocalRingFst (P.redFst Q)) ∧
      (∀ ht : (PlaceSpecialization.jFun (q := q) -
          algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (j₀ : AlgebraicClosure ℚ)) ∈
          R.smoothLocalRingFst (P.redFst Q), φ ⟨_, ht⟩ = PowerSeries.X) ∧
      (∀ (a : A) (ha : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (a : AlgebraicClosure ℚ) ∈
          R.smoothLocalRingFst (P.redFst Q)), φ ⟨_, ha⟩ = PowerSeries.C (R := ↥A) a) := by sorry
