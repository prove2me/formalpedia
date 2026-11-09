-- Prove2me | Theorems.Thm_LinearChoresCLS_lemma_7_1
-- name    : LinearChoresCLS.lemma_7_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T21:57:04.493435+00:00
-- url     : https://prove2.me/theorems/b1a62c6f-aed3-4328-b5ab-0a7b545b2632
-- title:
--   Lemma 7.1 — equilibrium recovery
-- statement:
--   Let $I=(A,c,\varepsilon)$ with $n\ge1$, $\varepsilon>0$, let $(p^\star,z^\star)$ be a competitive equilibrium of the completed market $f(I)$, and let
--   $$
--   x^\star=g(I,(p^\star,z^\star))=\frac1t\Big(\frac{p^\star_1}{p^\star_0}-1,\dots,\frac{p^\star_n}{p^\star_0}-1\Big).
--   $$
--   Then $x^\star\in[0,1]^n$ and $p^\star=\tilde p(x^\star)$.
--
--   Every equilibrium price vector of the completed market therefore lies in the constructed price family, which is property (a)(i) of Proposition 4.1 apart from the running time.
--
--   Differences from the source: none.
-- source:
--   Liu–Ma–Tao–Yang–Zheng, Competitive Equilibrium for Linear Chores is CLS-complete, arXiv:2611.06589 (held version, sha256 85d34a9e048d151ecff70a8614b9c2dd44307d5cf60faba74d14b2dd7eedc0b5), Lemma 7.1, p.32 (proof pp.36–37)

import Mathlib
import Definitions.Def_LinearChoresCLS_PriceFamily

open Finset NetworkEquilibriumCLS.LinearNash

namespace LinearChoresCLS

/-- **Lemma 7.1 (Equilibrium recovery)** (arXiv:2611.06589, held version sha256 85d34a9e…, p.32).
Let `(p⋆, z⋆)` be an equilibrium of the completed market `f(I)` (`n ≥ 1`, `ε > 0`, parameters
(7.1)) and `x⋆ := g(I, (p⋆, z⋆)) = (1/t)(p⋆₁/p⋆₀ − 1, …, p⋆ₙ/p⋆₀ − 1)` (7.3). Then `x⋆ ∈ [0,1]ⁿ`
and `p⋆ = p̃(x⋆)`. -/
theorem lemma_7_1 {n : ℕ} (hn : 0 < n) (P : Quadratic n) (ε : ℚ) (hε : 0 < ε)
    (p : Chore n (chainLength P ε) → ℝ) (z : Agent n (chainLength P ε) → Chore n (chainLength P ε) → ℝ)
    (hCE : (completedMarket P ε).IsCE p z) :
    InCube (decoder (tParam P ε) p) ∧ p = completedNormPrice P ε (decoder (tParam P ε) p) := by sorry

end LinearChoresCLS
