-- Prove2me | Theorems.Thm_MagnonCode_AQEDC_theorem_7_9
-- name    : MagnonCode.AQEDC.theorem_7_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:41:21.60266+00:00
-- url     : https://prove2.me/theorems/380571d1-88f6-417a-888e-4872ec115649
-- title:
--   Theorem 7.9: parameters of the magnon-code
-- statement:
--   Let $\nu\in(0,1)$ and $\lambda,\kappa>0$ with $6\kappa+\lambda<\nu$. Then there are $C>0$ and $n_0$ such that for every $n\ge n_0$, with
--
--   $$
--   K=\lceil n^\kappa\rceil,\qquad d=\lceil n^{1-\nu}\rceil,\qquad k=\log_2K,
--   $$
--
--   the following hold:
--
--   1. the descendant states $S_-^{2i}|\Psi\rangle$, $i<K$, exist, that is $2i\le n-2$;
--   2. $\kappa\log_2n\le k\le\kappa\log_2n+1$;
--   3. these states span a subspace of dimension $K$, which is an $(\epsilon,\delta)[[n,k,d]]$-AQEDC with
--
--   $$
--   \epsilon=C\,n^{-(\nu-(6\kappa+\lambda))},\qquad\delta=n^{-\lambda}.
--   $$
--
--   The magnetizations $2i$ pairwise differ by at least $2$. Both $\epsilon$ and $\delta$ tend to $0$, so low-energy eigenstates of the Heisenberg-XXX chain detect errors of polynomial weight, with polynomially many logical dimensions.
--
--   Differences from the source:
--   - reading: k = κ log₂ n, d = n^{1−ν} → K = ⌈n^κ⌉, d = ⌈n^{1−ν}⌉, k = log₂ K with κ log₂ n ≤ k ≤ κ log₂ n + 1; reason: these numbers are not integers in general; rounding up gives more code dimension and more errors, the stronger direction, and k = κ log₂ n exactly when n^κ is an integer
--   - reading: ϵ = Θ(n^{−(ν−(6κ+λ))}), for unspecified n → ∃ C > 0, n₀ ∀ n ≥ n₀, ε_n = C n^{−(ν−(6κ+λ))} exactly; reason: Θ names ε_n, and p.10 notes a larger ε is implied; the states exist only for large n
--   - generalization: there is a subspace C spanned by descendant states with magnetization pairwise differing by at least 2 → the named subspace span{Ψ_{2i} : i < K}, with rank K; reason: this is the subspace of the proof on p. 70, and it implies the existence claim
--   - encoding: subspace of dimension p^k → projector P with its range the span and rank K, and (via IsAQEDC) rank P = 2^k as reals; reason: Definition 3.1 gives the code with its projection; same instances
--   - encoding: (ε, δ)-approximate error-detection code (Definition 3.1) → IsDetecting, which also assumes t = tr(P N(|Ψ⟩⟨Ψ|)) ≠ 0 before concluding; reason: δ > 0 here and δ ≤ t, so t ≠ 0 always holds and the clause changes no instance; it only excludes the case where the printed ρ_{N,P} = t⁻¹ P N(|Ψ⟩⟨Ψ|) P is undefined
-- source:
--   Gschwendtner, König, Şahinoğlu, Tang, Quantum Error-Detection at Low Energies, arXiv:1902.02115v2, Theorem 7.9, p. 69; the subspace from its proof, p. 70

import Mathlib
import Definitions.Def_MagnonCode_AQEDC_IsAQEDC
import Definitions.Def_MagnonCode_AQEDC_PsiDesc

namespace MagnonCode.AQEDC

/-- **Theorem 7.9 (Parameters of the magnon-code)** (Gschwendtner, König, Şahinoğlu, Tang, *Quantum Error-Detection at Low Energies*, arXiv:1902.02115v2, p. 69): let `ν ∈ (0, 1)` and `λ, κ > 0` with
`6κ + λ < ν`. Then there are `C > 0` and `n₀` such that for `n ≥ n₀`, with `K = ⌈n^κ⌉`, `d = ⌈n^{1−ν}⌉`,
`k = log₂ K`: the descendant states `S₋^{2i}|Ψ⟩`, `i < K`, exist; `k` lies within 1 above `κ log₂ n`;
and these states span a `K`-dimensional `(C n^{−(ν−(6κ+λ))}, n^{−λ})[[n, k, d]]`-AQEDC.

**Formalization Note** The magnetizations `2i` pairwise differ by at least 2 by construction. `n^κ` and
`n^{1−ν}` need not be integers, so they are rounded up: more code dimension and more errors. `ε` is
`Θ(n^{−(ν−(6κ+λ))})` because it equals `C` times that power. `C` and `n₀` depend on `ν, κ, λ` only. -/
theorem theorem_7_9 (ν κ lam : ℝ) (hν0 : 0 < ν) (hν1 : ν < 1) (hκ : 0 < κ) (hlam : 0 < lam)
    (h : 6 * κ + lam < ν) :
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      let K := ⌈(n : ℝ) ^ κ⌉₊
      let d := ⌈(n : ℝ) ^ (1 - ν)⌉₊
      let k := Real.logb 2 (K : ℝ)
      (∀ i, i < K → 2 * i + 2 ≤ n) ∧
      κ * Real.logb 2 (n : ℝ) ≤ k ∧ k ≤ κ * Real.logb 2 (n : ℝ) + 1 ∧
      ∃ P : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ,
        LinearMap.range P.mulVecLin =
          Submodule.span ℂ (Set.range fun i : Fin K => PsiDesc n (2 * i.val)) ∧
        P.rank = K ∧
        IsAQEDC 2 n k d (C * (n : ℝ) ^ (-(ν - (6 * κ + lam)))) ((n : ℝ) ^ (-lam)) P := by sorry

end MagnonCode.AQEDC
