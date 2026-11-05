-- Prove2me | Theorems.Thm_MosonyiPetz_sufficient_structure
-- name    : MosonyiPetz.sufficient_structure
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:45:32.927957+00:00
-- url     : https://prove2.me/theorems/60f0befa-f7e0-41e7-a46c-41ba0a3381f6
-- title:
--   Theorem 1: a sufficient coarse-graining factorizes $T(D_s)=\sum_p\lambda_s(p)S_s(p)R(p)$ over the central blocks of $\mathcal D_{\mathcal K}$
-- statement:
--   Let $T:\mathcal B(\mathcal H)\to\mathcal B(\mathcal K)$ be a linear, trace-preserving, 2-positive map between the matrix algebras of finite-dimensional Hilbert spaces which is sufficient for the invertible density matrices $D_1,D_2$ on $\mathcal H$, and assume that $T(D_1)$ and $T(D_2)$ are invertible. Then there exist a unital $*$-subalgebra $\mathcal D_{\mathcal K}\subset\mathcal B(\mathcal K)$, with minimal central projections $z_1,\dots,z_r$ (all of them: pairwise orthogonal, summing to $I$), such that
--
--   1. $T^*(XY)=T^*(X)T^*(Y)$ for every $X\in\mathcal B(\mathcal K)$ and every $Y\in\mathcal D_{\mathcal K}$;
--   2. for $s=1,2$,
--   $$T(D_s)=\sum_{p=1}^r\lambda_s(p)\,S_s(p)\,R(p),$$
--   where $\lambda_1,\lambda_2$ are probability distributions on $\{1,\dots,r\}$, $S_s(p)\ge0$ lies in $z_p\mathcal D_{\mathcal K}$, $R(p)\ge0$ lies in $z_p\mathcal D_{\mathcal K}'$ (it commutes with $\mathcal D_{\mathcal K}$ and $z_pR(p)=R(p)$), the factor $R(p)$ is the **same** for $s=1$ and $s=2$, and each summand is normalized: $\operatorname{Tr}S_s(p)R(p)=1$.
--
--   $T^*$ is the Hilbert–Schmidt adjoint of $T$. The point is that sufficiency leaves the two output densities differing only in the factors $S_s(p)$ inside the algebra $\mathcal D_{\mathcal K}$ on which $T^*$ is multiplicative, while the commutant factors coincide. Clause 1 alone holds for $\mathcal D_{\mathcal K}=\mathbb C I$, and clause 2 alone for $\mathcal D_{\mathcal K}=\mathcal B(\mathcal K)$; the theorem asserts both for one algebra.
--
--   **Formalization Note** $\mathcal B(\mathcal H)$ is `Matrix H H ℂ`; the densities are `D 0`, `D 1` (positive definite, trace one), with `T (D s)` positive definite; sufficiency is eq. (1); $T^*$ is `channelAdjoint`. "Density operators $S_s(p)\in z_p\mathcal D_{\mathcal K}$ and $R(p)\in z_p\mathcal D_{\mathcal K}'$" is read as positive factors normalized jointly by $\operatorname{Tr}S_s(p)R(p)=1$, equivalently each a density of its own tensor factor of $z_p\mathcal K$ (p.9: "If we want both factors to be normalized, then positive coefficients should be included in the front").
--
--   Differences from the source:
--   - encoding: the two densities D_1, D_2 (s = 1, 2) → D : Fin 2 → Matrix H H ℂ with D 0 = D₁, D 1 = D₂; reason: indexing convention; same instances
--   - encoding: invertible density matrices D_s and invertible T(D_s) → (D s).PosDef ∧ (D s).trace = 1 and (T (D s)).PosDef; reason: an invertible positive semidefinite matrix is positive definite; same instances
--   - encoding: T*, the adjoint of T for ⟨A, B⟩ = Tr A*B → channelAdjoint T (published Hilbert–Schmidt adjoint); reason: the same map
--   - reading: a subalgebra D_K ⊂ B(K) → DK : StarSubalgebra ℂ (Matrix K K ℂ) (unital *-subalgebra); reason: the proof's D_K is the fixed point algebra of the unital map γ_K, a unital *-algebra; requiring it is the stronger witness
--   - reading: minimal central projections z1, z2, . . . , zr ∈ D_K → IsCentralDecomposition DK z: all minimal central projections, pairwise orthogonal, summing to 1; reason: p.9: 'Assume that z1, z2, . . . , zr the minimal central projections in DK'; the complete family is the stronger reading
--   - reading: density operators S_s(p) ∈ z_pD_K and R(p) ∈ z_pD′_K → S s p, R p positive semidefinite, S s p ∈ DK, z p * S s p = S s p, R p ∈ centralizer DK, z p * R p = R p, Tr (S s p * R p) = 1; reason: each factor is a density of its own tensor factor (p.9 remark on normalization), which is equivalent to joint normalization Tr(S R) = 1; the reading 'trace one on K' is false: T = id on M₂, D₁ = diag(1/3, 2/3), D₂ = [[1/2, 1/4], [1/4, 1/2]] admits no unital *-subalgebra witness
--   - encoding: probability distributions λ_s(p) (1 ≤ p ≤ r) → lam : Fin 2 → Fin r → ℝ, nonnegative, ∑ p, lam s p = 1; reason: same objects
-- source:
--   Mosonyi–Petz, Structure of sufficient quantum coarse-grainings, arXiv:quant-ph/0312221v1, §4, p.10, Theorem 1

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P84
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P21
import Definitions.Def_MosonyiPetz_IsSufficient
import Definitions.Def_MosonyiPetz_IsCentralDecomposition

open scoped Matrix ComplexOrder
open QAlgorithms.Papers.Independent.Intakethird100.P84 (IsTwoPositive)
open QAlgorithms.Papers.Independent.Dependency50.P21 (channelAdjoint)

namespace MosonyiPetz

/-- **Theorem 1: structure of sufficient coarse-grainings.**
Mosonyi–Petz, *Structure of sufficient quantum coarse-grainings*, arXiv:quant-ph/0312221v1, §4, p.10, Theorem 1: "Let T : B(H) → B(K) be a trace-preserving 2-positive mapping which is
sufficient for the invertible density matrices Ds on H (s = 1, 2). Assume that T(D1) and T(D2)
are invertible as well. Then there exists a subalgebra DK ⊂ B(K) with minimal central projections
z1, z2, . . . , zr ∈ DK such that (a) T*(XY) = T*(X)T*(Y) for X ∈ B(K) and Y ∈ DK.
(b) T(Ds) = Σ_{p=1}^r λs(p)Ss(p)R(p) for some density operators Ss(p) ∈ zpDK and R(p) ∈ zpD′K and
for probability distributions λs(p) (1 ≤ p ≤ r) for s = 1, 2."

Under the standing assumption and sufficiency there are a unital *-subalgebra `D_K` of `B(K)`, a
number `r` and the family `z_1, …, z_r` of **all** minimal central projections of `D_K` such that
(a) `T*(X Y) = T*(X) T*(Y)` for every `X ∈ B(K)` and every `Y ∈ D_K`, and
(b) there are probability vectors `λ_1, λ_2` on `{1, …, r}`, positive semidefinite
`S_s(p) ∈ z_p D_K` and `R(p) ∈ z_p D_K′` (with `R(p)` the same for `s = 1, 2`) normalized by
`Tr (S_s(p) R(p)) = 1`, such that `T(D_s) = Σ_p λ_s(p) S_s(p) R(p)` for `s = 1, 2`.

**Formalization Note.** `B(H)` is `Matrix H H ℂ`; the densities are `D 0 = D₁`, `D 1 = D₂`,
positive definite of trace one, and `T (D s)` positive definite; `T` is linear, 2-positive and
trace preserving; sufficiency is (1). `T*` is the Hilbert–Schmidt adjoint `channelAdjoint T`.
`D_K` is a unital *-subalgebra (`StarSubalgebra`); `z_p D_K` means `S ∈ D_K` with `z_p S = S`, and
`z_p D_K′` means `R` commutes with `D_K` and `z_p R = R`. "Density operators" is read as positive
factors normalized jointly by `Tr (S_s(p) R(p)) = 1` (each factor a density of its own tensor
factor, p.9: "If we want both factors to be normalized, then positive coefficients should be
included in the front"); the reading "trace one on `K`" makes the theorem false already for
`T = id` on `M₂`. -/
theorem sufficient_structure
    {H K : Type*} [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
    (T : Matrix H H ℂ →ₗ[ℂ] Matrix K K ℂ) (hT : IsTwoPositive T)
    (htr : ∀ A, (T A).trace = A.trace)
    (D : Fin 2 → Matrix H H ℂ) (hD : ∀ s, (D s).PosDef ∧ (D s).trace = 1)
    (hTD : ∀ s, (T (D s)).PosDef)
    (hsuff : IsSufficient T (D 0) (D 1)) :
    ∃ (DK : StarSubalgebra ℂ (Matrix K K ℂ)) (r : ℕ) (z : Fin r → Matrix K K ℂ),
      IsCentralDecomposition DK z ∧
      (∀ X : Matrix K K ℂ, ∀ Y ∈ DK,
        channelAdjoint T (X * Y) = channelAdjoint T X * channelAdjoint T Y) ∧
      ∃ (lam : Fin 2 → Fin r → ℝ) (S : Fin 2 → Fin r → Matrix K K ℂ) (R : Fin r → Matrix K K ℂ),
        (∀ s p, 0 ≤ lam s p) ∧ (∀ s, ∑ p, lam s p = 1) ∧
        (∀ s p, S s p ∈ DK ∧ z p * S s p = S s p ∧ (S s p).PosSemidef) ∧
        (∀ p, R p ∈ Set.centralizer (DK : Set (Matrix K K ℂ)) ∧ z p * R p = R p ∧
          (R p).PosSemidef) ∧
        (∀ s p, (S s p * R p).trace = 1) ∧
        ∀ s, T (D s) = ∑ p, (lam s p : ℂ) • (S s p * R p) := by sorry

end MosonyiPetz
