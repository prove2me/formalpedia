-- Prove2me | Theorems.Thm_HZTractability_lemma_4_11
-- name    : HZTractability.lemma_4_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T04:09:05.348599+00:00
-- url     : https://prove2.me/theorems/0b463ebd-4ecd-4fe8-afe7-7718c5f6f345
-- title:
--   Lemma 4.11 — rational approximate witnesses of logarithmic bit length
-- statement:
--   There is an absolute constant $c$ such that for every $N\ge1$, every rational $N\times N$ utility matrix $u$ with entries in $[0,1]$, and every rational $\varepsilon$ with $0<\varepsilon\le1$, the HZ market $u$ has a normalized additive $\varepsilon$-equilibrium $(p,x)$ with rational coordinates, each of bit length at most
--   $$
--   c\,\big(1+\log_2N+\log_2(1/\varepsilon)\big).
--   $$
--
--   This makes the search problem total with polynomial-length witnesses.
--
--   Differences from the source:
--   - encoding: bit length $O(1+\log N+\log(1/\varepsilon))$ → an absolute constant $c$ chosen before $N,u,\varepsilon$; bit length the public `WeightedCongestionBR.bitLen` ($1+$ binary digits of the reduced numerator $+$ binary digits of the denominator); base-two logarithms; reason: the base and the precise bit-length convention change only the constant
-- source:
--   Panageas, Shein, Taherijam, Vazirani, Exploring the Tractability Frontier of Hylland–Zeckhauser Models, arXiv:2610.35848 (held version, sha256 74b7bf9f…), Lemma 4.11, p.19 (PDF p.21); proof App. C, p.45

import Mathlib
import Definitions.Def_HZTractability_IsNormAddEq
import Definitions.Def_WeightedCongestionBR_bitLen

namespace HZTractability

/-- **Lemma 4.11 (Rational approximate witnesses)** (Panageas–Shein–Taherijam–Vazirani,
arXiv:2610.35848, held version, sha256 74b7bf9f…, p.19 (PDF 21); proof App. C, p.45): "For
rational 0 < ε ≤ 1, every N-buyer HZ market with utilities in [0, 1] has a normalized additive
ε-equilibrium whose coordinates have bit length O(1 + log N + log(1/ε))."

There is an absolute constant `c` such that for every `N ≥ 1`, every rational `N × N` utility
matrix `u` with entries in `[0, 1]` and every rational `ε ∈ (0, 1]`, there are a rational
allocation `x` and rational prices `p` forming a normalized additive ε-equilibrium of `u`, every
coordinate of which has bit length at most `c (1 + log₂ N + log₂(1/ε))`.

**Formalization Note** The `O(·)` constant `c` is chosen before `N`, `u` and `ε`. Bit length is the
public `WeightedCongestionBR.bitLen`, `1 + size|num| + size den` of the reduced fraction (the paper
does not define bit length; other conventions differ by an additive constant). Logarithms are to
base two, which changes `c` only. -/
theorem lemma_4_11 :
    ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, 1 ≤ N → ∀ u : Fin N → Fin N → ℚ, (∀ i j, 0 ≤ u i j ∧ u i j ≤ 1) →
      ∀ ε : ℚ, 0 < ε → ε ≤ 1 →
      ∃ (x : Fin N → Fin N → ℚ) (p : Fin N → ℚ),
        IsNormAddEq (fun i j => (u i j : ℝ)) (ε : ℝ) (fun i j => (x i j : ℝ)) (fun j => (p j : ℝ)) ∧
        (∀ i j, (WeightedCongestionBR.bitLen (x i j) : ℝ) ≤ c * (1 + Real.logb 2 N + Real.logb 2 (1 / (ε : ℝ)))) ∧
        ∀ j, (WeightedCongestionBR.bitLen (p j) : ℝ) ≤ c * (1 + Real.logb 2 N + Real.logb 2 (1 / (ε : ℝ))) := by sorry

end HZTractability
