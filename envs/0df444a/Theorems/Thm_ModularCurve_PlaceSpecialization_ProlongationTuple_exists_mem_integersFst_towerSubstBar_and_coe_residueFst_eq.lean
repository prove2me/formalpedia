-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_mem_integersFst_towerSubstBar_and_coe_residueFst_eq
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.exists_mem_integersFst_towerSubstBar_and_coe_residueFst_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/babe42da-80ad-5e99-b6a1-c31d1992b60e
-- title:
--   Substitution degeneracy and first residues: compatibility with q↦ q^ℓ
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, a positive integer $N$, a field $k$ of characteristic $q$ and a ring homomorphism $\mathrm{red}\colon A \to k$. Let `data` be modular polynomial data at level $q$ (a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(q)$ annihilating the pair $(j, j_q)$ of $q$-expansions), `hKr` the Kronecker congruence that the reduction of $\Phi$ modulo $q$ equals $(C X^q - X)(C X - X^q)$, and $h\alpha$, $h\beta$ the integrality of the Hecke maps `heckeAlphaBar`, `heckeBetaBar` at level $N$ and index $q$; let $P$ be a place specialisation for these data and $R$ a prolongation tuple over $P$. Fix a positive integer $\ell$ and, independently, data `dataᵣ`, `hKrᵣ`, `hαᵣ`, `hβᵣ` at level $N\ell$, a place specialisation $P_r$ for them and a prolongation tuple $R_r$ over $P_r$; no compatibility between $P$ and $P_r$ is assumed. Let $f$ lie in the base change to $\overline{\mathbb{Q}}$ of the full modular function field of level $Nq$ inside $\overline{\mathbb{Q}}((q))$, and assume $f$ belongs to the valuation subring `R.R₁.integers` of the first regular prolongation of $R$. Then the image of $f$ under `towerSubstBar` for the index $\ell$ and the divisibility $Nq\ell \mid N\ell q$ — that is, the level-$\ell$ substitution `heckeBetaBar` followed by the tower inclusion — belongs to `Rᵣ.R₁.integers`, and the Laurent series over $k$ of its image under `Rᵣ.residue₁`, an element of `modularFunctionFieldC k (N*ℓ)`, is obtained from the Laurent series of `R.residue₁ ⟨f, h⟩` in `modularFunctionFieldC k N` by applying `qExpand k ℓ`, the ring homomorphism multiplying all exponents by $\ell$.
--
--   This is the compatibility of the constant reductions (Gauss valuations at the cusp $\infty$) at levels $Nq$ and $N\ell q$ with the substitution degeneracy map $q \mapsto q^{\ell}$, read off on $q$-expansions. It is used to compare depths of places along the substitution leg of the level-$\ell$ Hecke correspondence, in the two results on `yDepth` of the restriction along `towerSubstBar`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_mem_integersFst_towerSubstBar_and_coe_residueFst_eq.lean

import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_DegeneracyTower

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.exists_mem_integersFst_towerSubstBar_and_coe_residueFst_eq
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)
    (ℓ : ℕ) [NeZero ℓ]
    {dataᵣ : ModularPolynomialData q} {hKrᵣ : KroneckerCongruence q dataᵣ}
    {hαᵣ : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) (N * ℓ) q}
    {hβᵣ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) (N * ℓ) q}
    {Pᵣ : PlaceSpecialization A q (N * ℓ) dataᵣ hKrᵣ k red hαᵣ hβᵣ} (Rᵣ : ProlongationTuple Pᵣ)
    (f : ↥(modularFunctionFieldBar (N * q))) (h : f ∈ R.R₁.integers) :
    ∃ h' : towerSubstBar (AlgebraicClosure ℚ) (N * q) ℓ
        (dvd_of_eq (Nat.mul_right_comm N q ℓ) : N * q * ℓ ∣ N * ℓ * q) f ∈ Rᵣ.R₁.integers,
      ((Rᵣ.residue₁ ⟨_, h'⟩ : ↥(modularFunctionFieldC k (N * ℓ))) : LaurentSeries k)
        = qExpand k ℓ ((R.residue₁ ⟨f, h⟩ : ↥(modularFunctionFieldC k N)) : LaurentSeries k) := by sorry
