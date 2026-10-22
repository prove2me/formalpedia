-- Prove2me | Theorems.Thm_InvariantSDP_BlockDiag_obs_i_ii
-- name    : InvariantSDP.BlockDiag.obs_i_ii
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:39:34.041739+00:00
-- url     : https://prove2.me/theorems/3da42f67-8964-4d5d-85d1-73f406407291
-- title:
--   Proof of Theorem 2.7, p. 14, observations (i)–(ii) — diagonal blocks are scalar, the $S_0$ rows and columns vanish
-- statement:
--   Let $\mathcal A \subseteq \mathbb C^{n\times n}$ be a matrix ∗-algebra, and let $\mathcal B$ be an inclusionwise maximal commutative ∗-subalgebra of $\mathcal A$ that is in diagonal form $\mathcal B = \{\lambda_1 I_1 + \dots + \lambda_k I_k : \lambda_i \in \mathbb C\}$ for a partition $[n] = S_0 \cup S_1 \cup \dots \cup S_k$ with $S_1, \dots, S_k$ nonempty, $I_i$ the zero-one diagonal matrix of $S_i$. Then for every $X \in \mathcal A$:
--
--   1. (i) for each $i = 1, \dots, k$ there is $c \in \mathbb C$ with $I_i X I_i = c\, I_i$, and $I_0 X I_0 = 0$;
--   2. (ii) $I_0 X = 0$ and $X I_0 = 0$.
--
--   In the paper's block notation $X_{ij}$ (the restriction of $I_iXI_j$ to rows $S_i$ and columns $S_j$): $X_{ii}$ is a multiple of the identity, $X_{00} = 0$, and $X_{0i}$, $X_{i0}$ are zero for all $i = 0, \dots, k$. Consequently $I_1 + \dots + I_k$ acts as the identity on $\mathcal A$.
--
--   **Formalization Note** The block $X_{ij}$ is represented by the full $n\times n$ product $I_iXI_j$, which carries the same entries padded with zeros. The paper's "we may assume $\mathcal B$ is in diagonal form" (after a unitary change of basis supplied by Theorem 2.2) is taken as the hypothesis `IsDiagForm B S`. Since $I_0 + I_1 + \dots + I_k = I$, item (ii) for all $i$ is exactly $I_0X = 0 = XI_0$. Partition indices are 0-based, with `none` for $S_0$.
-- source:
--   Bachoc, Gijswijt, Schrijver & Vallentin, Invariant semidefinite programs, arXiv:1007.2905v2, p. 14, proof of Theorem 2.7, observations (i) and (ii)

import Mathlib
import Definitions.Def_InvariantSDP_BlockDiag_Basic

namespace InvariantSDP.BlockDiag

/-- Proof of Theorem 2.7, p. 14, observations (i) and (ii): with `ℬ` a maximal commutative ∗-subalgebra of
`𝒜` in the diagonal form `ℬ = ℂI₁ + ⋯ + ℂI_k`, for every `X ∈ 𝒜` each diagonal block `I_i X I_i` is a
multiple of `I_i`, `I₀ X I₀ = 0`, and `I₀ X = X I₀ = 0`. -/
theorem obs_i_ii {n k : ℕ} (A B : NonUnitalStarSubalgebra ℂ (Matrix (Fin n) (Fin n) ℂ))
    (S : Fin n → Option (Fin k)) (hB : IsMaxCommutative A B) (hS : IsDiagForm B S)
    (X : Matrix (Fin n) (Fin n) ℂ) (hX : X ∈ A) :
    ((∀ i : Fin k, ∃ c : ℂ,
        zeroOneDiag S (some i) * X * zeroOneDiag S (some i) = c • zeroOneDiag S (some i)) ∧
      zeroOneDiag S none * X * zeroOneDiag S none = 0) ∧
    (zeroOneDiag S none * X = 0 ∧ X * zeroOneDiag S none = 0) := by sorry

end InvariantSDP.BlockDiag
