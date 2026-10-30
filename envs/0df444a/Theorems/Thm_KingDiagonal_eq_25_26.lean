-- Prove2me | Theorems.Thm_KingDiagonal_eq_25_26
-- name    : KingDiagonal.eq_25_26
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T03:15:12.878622+00:00
-- url     : https://prove2.me/theorems/1b7f8f54-8f79-4566-8885-48d8a053da09
-- title:
--   Eqs. (25)–(26): $(V^*V)^p$ is block diagonal and $\mathrm{Tr}(V^*V)^pK^p = \sum_i \mathrm{Tr}(V_i^*V_i)^p((\Phi(A))^p)_{ii}$
-- statement:
--   Let $V = \operatorname{diag}(V_1,\dots,V_n)$ be block diagonal with blocks $V_i$ of size $r\times s$, let $G$ be a positive semidefinite $n\times n$ matrix, $I'$ the $s\times s$ identity and $K = G\otimes I'$. Then for every real $p\ge1$:
--
--   1. $(V^*V)^p$ is block diagonal: $$(V^*V)^p = \operatorname{diag}\big((V_1^*V_1)^p, \dots, (V_n^*V_n)^p\big);$$
--   2. $K^p = G^p\otimes I'$;
--   3. $$\operatorname{Tr}(V^*V)^pK^p = \sum_{i=1}^n \operatorname{Tr}(V_i^*V_i)^p\,\big(G^p\big)_{ii}.$$
--
--   In King's proof $G = \Phi(A)$ and the $V_i$ are the block rows of (16); the identity splits the right side of the Lieb–Thirring inequality into one term per block.
--
--   **Formalization Note** Matrix powers are taken with the continuous functional calculus.
--
--   Differences from the source:
--   - generalization: V_i the block rows of ((I ⊗ Ψ)(τ))^{1/2} and G = Φ(A) → arbitrary blocks V_i : Matrix r s ℂ and arbitrary positive semidefinite G; reason: the identities hold for every block-diagonal V and PSD G; the page's V and Φ(A) are an instance
--   - encoding: real matrix powers X^p, X^{p/2}, X^{1/2} of positive semidefinite matrices → cfc (fun x : ℝ => x ^ p) X, cfc Real.sqrt X; reason: the continuous functional calculus gives the usual powers on PSD (Hermitian, nonnegative spectrum) matrices, the only inputs used
-- source:
--   King, An application of a matrix inequality in quantum information theory, arXiv:quant-ph/0412046v1, eqs. (25)–(26), p.6

import Mathlib
import Definitions.Def_KingDiagonal_blockDiag

open scoped Matrix Kronecker ComplexOrder

namespace KingDiagonal

/-- King, arXiv:quant-ph/0412046v1, eqs. (25)–(26), p.6: let `V = diag(V_1, …, V_n)` be block
diagonal (23) and `K = G ⊗ I′` with `G` positive semidefinite (the paper's `G = Φ(A)`, (24)). Then
for `p ≥ 1`:
1. `(V*V)^p` is block diagonal, `(V*V)^p = diag((V_1*V_1)^p, …, (V_n*V_n)^p)` (25);
2. `K^p = G^p ⊗ I′`;
3. `Tr (V*V)^p K^p = Σ_{i=1}^n Tr (V_i*V_i)^p (G^p)_{ii}` (26).

**Formalization Note.** Stated for arbitrary blocks `V_i : r × s` (the paper's `V_i : k × kn`) and
any positive semidefinite `G`, with `I′` the `s × s` identity. Real powers are
`cfc (fun x : ℝ => x ^ p)`, applied only to positive semidefinite matrices. -/
theorem eq_25_26 {n r s : Type*} [Fintype n] [DecidableEq n] [Fintype r] [DecidableEq r]
    [Fintype s] [DecidableEq s] (V : n → Matrix r s ℂ) (G : Matrix n n ℂ) (hG : G.PosSemidef)
    (p : ℝ) (hp : 1 ≤ p) :
    cfc (fun x : ℝ => x ^ p) ((blockDiag V)ᴴ * blockDiag V) =
        blockDiag (fun i => cfc (fun x : ℝ => x ^ p) ((V i)ᴴ * V i)) ∧
      cfc (fun x : ℝ => x ^ p) (G ⊗ₖ (1 : Matrix s s ℂ)) =
        cfc (fun x : ℝ => x ^ p) G ⊗ₖ (1 : Matrix s s ℂ) ∧
      (cfc (fun x : ℝ => x ^ p) ((blockDiag V)ᴴ * blockDiag V) *
          cfc (fun x : ℝ => x ^ p) (G ⊗ₖ (1 : Matrix s s ℂ))).trace =
        ∑ i, (cfc (fun x : ℝ => x ^ p) ((V i)ᴴ * V i)).trace * cfc (fun x : ℝ => x ^ p) G i i := by sorry

end KingDiagonal
