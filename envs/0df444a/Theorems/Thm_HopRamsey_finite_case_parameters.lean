-- Prove2me | Theorems.Thm_HopRamsey_finite_case_parameters
-- name    : HopRamsey.finite_case_parameters
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T21:45:19.926642+00:00
-- url     : https://prove2.me/theorems/79f29e63-b314-4dff-b2db-acd54045ef63
-- title:
--   Conclusion of §4.3: $2k(L+1)$, $8kL=\varepsilon^{-1}\tilde O(\log n)$ and $g(n,\Phi)=\tilde O(\log n)$ when $\Phi=\mathrm{poly}(n)$
-- statement:
--   For every exponent $c$ there are constants $C>0$ and $K$ such that for every $n\ge2$, every $\varepsilon\in(0,1)$ and every $\Phi$ with $2\le\Phi\le n^c$, the parameters of Figure 2 (with $|V|=n$) satisfy
--
--   $$
--   2k(L+1)\le\frac{C\,\Lambda_K(n)}{\varepsilon},\qquad 8kL\le\frac{C\,\Lambda_K(n)}{\varepsilon},\qquad g(n,\Phi)\le C\,\Lambda_K(n),
--   $$
--
--   where $\Lambda_K(n)=\log_2(n+1)(1+\log_2(1+\log_2(n+1)))^K$. That is, hop-stretch and distortion are $\varepsilon^{-1}\tilde O(\log n)$ and the expected distortion is $\tilde O(\log n)$, independently of $\varepsilon$.
--
--   Differences from the source:
--   - reading: Φ = poly(n) → 2 ≤ Φ ≤ n^c for a fixed exponent c, with C and K allowed to depend on c; reason: "poly(n)" fixes the exponent; Φ ≥ 2 is a standing assumption
--   - reading: ε^{−1}·Õ(log n) and Õ(log n) → ≤ C·Λ_K(n)/ε and ≤ C·Λ_K(n), with C > 0 and K chosen before n, ε and Φ; reason: the paper's Õ(g) = O(g)·polylog(g) (p.12) with absolute constants
-- source:
--   Filtser, Zuzic, Trees with Benefits: Stochastic Hop-Constrained Ramsey-Type Embeddings with Logarithmic Expected Distortion, STOC 2027 submission (manuscript sha256 1ee73385…), Conclusion of §4.3, p.25 (PDF p.27)

import Mathlib
import Definitions.Def_HopRamsey_Fig2Params
import Definitions.Def_HopRamsey_polylogBound

open scoped ENNReal

namespace HopRamsey

/-- Filtser, Zuzic, *Trees with Benefits: Stochastic Hop-Constrained Ramsey-Type Embeddings with
Logarithmic Expected Distortion*, STOC 2027 submission (manuscript sha256 1ee73385…),
Parameter bounds of the Conclusion of §4.3, p.25 (PDF p.27): "It follows that Φ = poly(n). In
particular, k = ⌈(4/ε)·(1+2δ)^{log Φ}·(ln|V| + ln(2/δ)·log Φ)⌉ = ε^{−1}·Õ(log n). [...] hop-stretch
2k·(L+1) = ε^{−1}·Õ(log n). [...] distortion k·8L = ε^{−1}·Õ(log n). [...] g(n,Φ) = 2⁸·L·log n·
(1+2δ)^{log Φ} = Õ(log n)."

**Formalization Note.** `Φ = poly(n)` is `2 ≤ Φ ≤ n^c`; `Õ(log n)` is `C·Λ_K(n)` with
`Λ_K(n) = log₂(n+1)·(1+log₂(1+log₂(n+1)))^K` (`polylogBound`), where `C > 0` and `K` depend only on
`c`, and are chosen before `n`, `ε` and `Φ`. -/
theorem finite_case_parameters (c : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ K : ℕ, ∀ P : Fig2Params, 2 ≤ P.N → 0 < P.ε → P.ε < 1 → 2 ≤ P.Φ →
      P.Φ ≤ (P.N : ℝ) ^ c →
      (2 * P.k * (P.L + 1) : ℝ) ≤ C * polylogBound K P.N / P.ε ∧
      ((P.k : ℝ) * 8 * P.L) ≤ C * polylogBound K P.N / P.ε ∧
      P.g P.N P.Φ ≤ C * polylogBound K P.N := by sorry

end HopRamsey
