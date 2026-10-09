-- Prove2me | Theorems.Thm_HighOrderWalks_OneSided_theorem_5_2
-- name    : HighOrderWalks.OneSided.theorem_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T01:42:03.591388+00:00
-- url     : https://prove2.me/theorems/8fbfe1c2-3160-4c1a-af2a-633a98b58fe4
-- title:
--   Theorem 5.2 (Decomposition Theorem), p. 15 — ‖d_kφ‖² = Σ_j (k+1−j)‖φ^j‖² + Σ_j Σ_{τ∈X(j−1)} ⟨(M′)⁺_{τ,0}(I − M⁻_{τ,0})(φ^j)′_τ, (φ^j)′_τ⟩
-- statement:
--   Let $X$ be a pure $n$-dimensional weighted simplicial complex, $0\le k\le n-1$, and $\phi\in C^k_0(X,\mathbb R)$. Then there are cochains $\phi^j\in C^j_0(X,\mathbb R)$ for $0\le j\le k$ and $(\phi^j)'\in C^j_0(X,\mathbb R)$ for $0\le j\le k-1$ such that, writing $(\phi^k)'=\phi$:
--   1. for every $0\le j\le k$,
--   $$\|(\phi^j)'\|^2=\|\phi^j\|^2+\|\phi^{j-1}\|^2+\dots+\|\phi^0\|^2;$$
--   2. $$\|d_k\phi\|^2=\sum_{j=0}^{k}(k+1-j)\|\phi^j\|^2+\sum_{j=0}^{k}\sum_{\tau\in X(j-1)}\big\langle (M')^+_{\tau,0}(I-M^-_{\tau,0})(\phi^j)'_\tau,\ (\phi^j)'_\tau\big\rangle .$$
--
--   The theorem requires no expansion hypothesis; it splits $\|d\phi\|^2$ into a combinatorial part and a sum of link terms, which local spectral bounds then control (Corollary 5.3).
--
--   **Formalization Note.** The families $\phi^j$, $(\phi^j)'$ are functions $\mathbb N\to$ cochains; only indices $j\le k$ are constrained. Each $j$-cochain is read on $X(j)$ (faces with $j+1$ vertices), and $\|d_k\phi\|$ on $X(k+1)$.
-- source:
--   Kaufman–Oppenheim, High Order Random Walks: Beyond Spectral Gap, arXiv:1707.02799v3, p. 15, Theorem 5.2

import Mathlib
import Definitions.Def_HighOrderWalks_OneSided_Setting

namespace HighOrderWalks.OneSided

/-- Theorem 5.2 (Decomposition Theorem), p. 15: for `0 ≤ k ≤ n - 1` and `φ ∈ C^k_0(X, ℝ)` there
are `φ^j ∈ C^j_0` (`0 ≤ j ≤ k`) and `(φ^j)' ∈ C^j_0` (`0 ≤ j < k`), with `(φ^k)' = φ`, such that
`‖(φ^j)'‖² = ‖φ^j‖² + … + ‖φ^0‖²` for `0 ≤ j ≤ k` and
`‖d_k φ‖² = Σ_{j=0}^k (k+1-j) ‖φ^j‖² + Σ_{j=0}^k Σ_{τ ∈ X(j-1)} ⟨(M')⁺_{τ,0}(I - M⁻_{τ,0}) (φ^j)'_τ, (φ^j)'_τ⟩`. -/
theorem theorem_5_2 {V : Type*} [DecidableEq V] (X : Finset (Finset V)) (n : ℕ)
    (hX : IsPureComplex X n) (m : Finset V → ℝ) (hm : IsWeight X n m)
    (k : ℕ) (hk : k + 1 ≤ n) (φ : Finset V → ℝ) (hφ : ip X m (k + 1) φ (fun _ => 1) = 0) :
    ∃ phi phi' : ℕ → Finset V → ℝ,
      phi' k = φ ∧
      (∀ j ≤ k, ip X m (j + 1) (phi j) (fun _ => 1) = 0) ∧
      (∀ j < k, ip X m (j + 1) (phi' j) (fun _ => 1) = 0) ∧
      (∀ j ≤ k, ip X m (j + 1) (phi' j) (phi' j) =
        ∑ i ∈ Finset.range (j + 1), ip X m (i + 1) (phi i) (phi i)) ∧
      ip X m (k + 2) (dS X φ) (dS X φ) =
        ∑ j ∈ Finset.range (k + 1), ((k : ℝ) + 1 - j) * ip X m (j + 1) (phi j) (phi j) +
          ∑ j ∈ Finset.range (k + 1), linkTerm X m j (phi' j) (phi' j) := by sorry

end HighOrderWalks.OneSided
