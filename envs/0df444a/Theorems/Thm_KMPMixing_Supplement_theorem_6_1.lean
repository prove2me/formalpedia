-- Prove2me | Theorems.Thm_KMPMixing_Supplement_theorem_6_1
-- name    : KMPMixing.Supplement.theorem_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:58:08.628997+00:00
-- url     : https://prove2.me/theorems/74b0118f-dac4-45cb-9481-712329505d91
-- title:
--   Theorem 6.1 — the parallel Kac twirl is within $2d^2e^{-ck}$ of the Haar twirl on $\vee^t\mathbb C^d$
-- statement:
--   There is an absolute constant $c>0$ such that the following holds. Let $n,t$ be positive integers, $k\in\mathbb N$, and $d=2^n$. Let $\Phi^{t,k}_{\mathrm{Kac}}$ be the $k$-fold composition of the parallel Kac twirl and $\Phi^t_{\mathrm{Haar}}$ the Haar twirl on $(\mathbb C^d)^{\otimes t}$, and let $\Pi_{\mathrm{Sym}}$ be the projector onto the symmetric subspace $\vee^t\mathbb C^d$. For any state $\sigma$ on $(\mathbb C^d)^{\otimes t}\otimes\mathbb C^m$ (any $m$) with $\mathrm{Tr}[(\Pi_{\mathrm{Sym}}\otimes1)\sigma]=1$,
--   $$
--   \big\|(\Phi^{t,k+1}_{\mathrm{Kac}}\otimes1)(\sigma)-(\Phi^t_{\mathrm{Haar}}\otimes1)(\sigma)\big\|_1\le2d^2e^{-ck}.
--   $$
--
--   The bound does not depend on $t$: on the symmetric subspace, the parallel Kac walk approximates the Haar twirl after $O(\log d)$ steps for every number of copies.
--
--   **Formalization Note** $c$ is quantified before $n,t,k,m,\sigma$. A state is a positive semidefinite matrix of trace $1$. $\|\cdot\|_1$ is the trace norm $\mathrm{Tr}\sqrt{A^\dagger A}$ (`WildeQIT.traceNorm`).
--
--   Differences from the source:
--   - encoding: reference system of the state σ (unspecified) → ℂ^m for an arbitrary m ∈ ℕ; reason: every finite-dimensional reference system is ℂ^m
--   - encoding: Φ^{t,k+1}_Kac ⊗ 1 and Φ^t_Haar ⊗ 1 → the (k+1)-fold iterate of X ↦ E_K[(K^{⊗t}⊗I) X (K^{⊗t}⊗I)†], and X ↦ E_U[(U^{⊗t}⊗I) X (U^{⊗t}⊗I)†]; reason: by linearity these are the tensored channels, and (Φ∘Ψ)⊗1 = (Φ⊗1)∘(Ψ⊗1)
--   - encoding: Π_Sym, the projector onto span{|u⟩^{⊗t}} → (1/t!) Σ_{π ∈ S_t} P_π; reason: the symmetrizer is the orthogonal projector onto the symmetric subspace
-- source:
--   Chen, Liu, Qin, Schulman, Song, Yao, Zhao, A Tale of Two Walks: From Kac to KMP and Back, arXiv:2609.38044 (sha256 6a9abdd4…), Theorem 6.1, p.40 (PDF p.42), restated p.51 (PDF p.53); Eqs. (31)–(34), pp.39–40

import Mathlib
import Definitions.Def_WildeQIT_traceNorm
import Definitions.Def_KMPMixing_Supplement_kacChannel

namespace KMPMixing.Supplement

open scoped Kronecker ComplexOrder

/-- **Theorem 6.1** (arXiv:2609.38044, p.40 (PDF p.42); restated p.51 (PDF p.53)). There is an
absolute constant `c > 0` such that the following holds. Let `n, t` be positive integers, let
`k ∈ ℕ`, and let `d = 2^n`. For any state `σ` (on `(ℂ^d)^{⊗t}` tensored with a reference system)
such that `Tr[(Π_Sym ⊗ 1) · σ] = 1`,
`‖(Φ^{t,k+1}_Kac ⊗ 1)(σ) − (Φ^t_Haar ⊗ 1)(σ)‖₁ ≤ 2 d² e^{−ck}`.

**Formalization Note** `c` is quantified before `n`, `t`, `k`, the reference dimension `m` and
`σ`. The reference system is `ℂ^m` for an arbitrary `m`. A state is a positive semidefinite
matrix of trace `1`. `Φ^{t,k+1}_Kac ⊗ 1` is the `(k+1)`-fold iterate of the one-step map
`kacChannel` (which is `Φ^t_Kac ⊗ 1`), and `Φ^t_Haar ⊗ 1` is `haarChannel`. `‖·‖₁` is the trace
norm `WildeQIT.traceNorm` (`Tr √(A†A)`). -/
theorem theorem_6_1 :
    ∃ c : ℝ, 0 < c ∧
      ∀ n t : ℕ, 0 < n → 0 < t →
      ∀ k m : ℕ,
      ∀ σ : Matrix ((Fin t → Fin (2 ^ n)) × Fin m) ((Fin t → Fin (2 ^ n)) × Fin m) ℂ,
        σ.PosSemidef → σ.trace = 1 →
        ((symProj (2 ^ n) t ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) * σ).trace = 1 →
        WildeQIT.traceNorm ((kacChannel (2 ^ n) t m)^[k + 1] σ - haarChannel (2 ^ n) t m σ) ≤
          2 * ((2 ^ n : ℕ) : ℝ) ^ 2 * Real.exp (-c * k) := by sorry

end KMPMixing.Supplement
