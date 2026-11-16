-- Prove2me | Theorems.Thm_KMPMixing_Supplement_theorem_1_3
-- name    : KMPMixing.Supplement.theorem_1_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:58:42.126211+00:00
-- url     : https://prove2.me/theorems/0a63f2b6-3c22-4bbb-a7d1-510b8fe328d0
-- title:
--   Theorem 1.3 (formal: Corollary 6.2) — $O(\log d+\log(1/\varepsilon))$ parallel Kac steps reach the Haar twirl on $\vee^t\mathbb C^d$
-- statement:
--   There is an absolute constant $c>0$ such that for all positive integers $n,t$, with $d=2^n$, every $\varepsilon\in(0,1)$ and every $k\in\mathbb N$ with
--   $$
--   k\ge c^{-1}\log\frac{2d^2}{\varepsilon},
--   $$
--   every state $\sigma$ on $(\mathbb C^d)^{\otimes t}\otimes\mathbb C^m$ (any $m$) with $\mathrm{Tr}[(\Pi_{\mathrm{Sym}}\otimes1)\sigma]=1$ satisfies
--   $$
--   \big\|(\Phi^{t,k+1}_{\mathrm{Kac}}\otimes1)(\sigma)-(\Phi^t_{\mathrm{Haar}}\otimes1)(\sigma)\big\|_1\le\varepsilon.
--   $$
--   Thus $O(\log d+\log(1/\varepsilon))$ repetitions of the parallel Kac walk suffice, uniformly over $t$.
--
--   This is the statement used to build scalable pseudorandom unitaries from the parallel Kac walk.
--
--   **Formalization Note** The conventions are those of Theorem 6.1: a state is a positive semidefinite trace-one matrix, $\Phi^{t,k+1}_{\mathrm{Kac}}\otimes1$ is the $(k+1)$-fold iterate of the one-step twirl, and $\|\cdot\|_1$ is the trace norm. $\log$ is the natural logarithm.
--
--   Differences from the source:
--   - reading: Theorem 1.3 (informal): there exists k = O(log d + log(1/ε)) with Φ^{t,k}_Kac(σ) and Φ^t_Haar(σ) ε-close → the formal version Corollary 6.2: for every natural k ≥ c⁻¹ log(2d²/ε), the (k+1)-step distance is ≤ ε, with the reference system; reason: the paper labels Theorem 1.3 as the informal version of Corollary 6.2
--   - reading: c is the constant in Theorem 6.1 → ∃ c > 0 quantified first, before n, t, ε, k, m, σ; reason: a standalone item cannot name another item's witness; Theorem 6.1 with its c implies this statement with the same c
--   - encoding: reference system, Φ ⊗ 1, Π_Sym → as in theorem_6_1: ℂ^m for arbitrary m, iterates of the twirl with ⊗I inside, the symmetrizer; reason: the same encodings as Theorem 6.1
-- source:
--   Chen, Liu, Qin, Schulman, Song, Yao, Zhao, A Tale of Two Walks: From Kac to KMP and Back, arXiv:2609.38044 (sha256 6a9abdd4…), Theorem 1.3, p.4 (PDF p.6); formal version Corollary 6.2, p.40 (PDF p.42)

import Mathlib
import Definitions.Def_WildeQIT_traceNorm
import Definitions.Def_KMPMixing_Supplement_kacChannel

namespace KMPMixing.Supplement

open scoped Kronecker ComplexOrder

/-- **Theorem 1.3** (arXiv:2609.38044, p.4 (PDF p.6)), stated at the strength of its formal
version **Corollary 6.2** (p.40 (PDF p.42)). There is an absolute constant `c > 0` such that for
all positive integers `n, t`, `d = 2^n`, every `ε ∈ (0, 1)` and every `k ∈ ℕ` with
`k ≥ c⁻¹ log(2d²/ε)`, every state `σ` with `Tr[(Π_Sym ⊗ 1) · σ] = 1` satisfies
`‖(Φ^{t,k+1}_Kac ⊗ 1)(σ) − (Φ^t_Haar ⊗ 1)(σ)‖₁ ≤ ε`. Thus `O(log d + log(1/ε))` repetitions
suffice uniformly over `t`.

**Formalization Note** Corollary 6.2 takes `c` to be the constant of Theorem 6.1; as a
standalone statement the constant is existentially quantified, before `n`, `t`, `ε`, `k`, the
reference dimension `m` and `σ`. Conventions are those of `theorem_6_1`: a state is a positive
semidefinite trace-`1` matrix on `(ℂ^d)^{⊗t} ⊗ ℂ^m` for arbitrary `m`, `Φ^{t,k+1}_Kac ⊗ 1` is the
`(k+1)`-fold iterate of `kacChannel`, and `‖·‖₁` is `WildeQIT.traceNorm`. `log` is the natural
logarithm. -/
theorem theorem_1_3 :
    ∃ c : ℝ, 0 < c ∧
      ∀ n t : ℕ, 0 < n → 0 < t →
      ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∀ k : ℕ, c⁻¹ * Real.log (2 * ((2 ^ n : ℕ) : ℝ) ^ 2 / ε) ≤ k →
      ∀ m : ℕ,
      ∀ σ : Matrix ((Fin t → Fin (2 ^ n)) × Fin m) ((Fin t → Fin (2 ^ n)) × Fin m) ℂ,
        σ.PosSemidef → σ.trace = 1 →
        ((symProj (2 ^ n) t ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) * σ).trace = 1 →
        WildeQIT.traceNorm
          ((kacChannel (2 ^ n) t m)^[k + 1] σ - haarChannel (2 ^ n) t m σ) ≤ ε := by sorry

end KMPMixing.Supplement
