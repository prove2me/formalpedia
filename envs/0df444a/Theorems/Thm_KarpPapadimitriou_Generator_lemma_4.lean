-- Prove2me | Theorems.Thm_KarpPapadimitriou_Generator_lemma_4
-- name    : KarpPapadimitriou.Generator.lemma_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:42:34.71821+00:00
-- url     : https://prove2.me/theorems/e641ca07-9268-4a4d-b318-b6cb6e67af47
-- title:
--   Lemma 4 — distance from a rational point to a small hyperplane
-- statement:
--   Fix dimension $n$, coefficient exponent $P$, objective $c$, threshold $k$, and the paper's parameter $t$. Let $r\in\mathbb Q^n$ have every reduced denominator at most $2^t$. If $H=\{x:f\cdot x=g\}$ is a small hyperplane with $r\notin H$, then
--   $$\operatorname{dist}(r,H)=\frac{|f\cdot r-g|}{\|f\|_2}\ge 2^{-(n+1)t}.$$
--
--   This supplies a lower gap when the generator produces a hyperplane not containing the current rational point.
--
--   **Formalization Note** The report prints “$x\notin H$” where its preceding point is $r$; the binder uses $r\notin H$. The Euclidean distance is stated by the equivalent quotient formula after casting $r$ to real coordinates.
-- source:
--   Karp & Papadimitriou, On linear characterizations of combinatorial optimization problems, MIT/LCS/TM-154 (Feb. 1980), p. 12, Lemma 4

import Mathlib
import Definitions.Def_KarpPapadimitriou_Generator_Hyperplanes

namespace KarpPapadimitriou.Generator

/-- Lemma 4: a rational point outside a small hyperplane has a quantified distance gap. -/
theorem lemma_4 (n P : ℕ) (c : Fin n → ℤ) (k : ℤ)
    (r : Fin n → ℚ) (f : Fin n → ℤ) (g : ℤ)
    (hsmall : SmallHyperplane P f g)
    (hden : ∀ i, (r i).den ≤ 2 ^ tParam n P c k)
    (hout : dotQ f r ≠ (g : ℚ)) :
    (1 : ℝ) / 2 ^ ((n + 1) * tParam n P c k) ≤
      hyperplaneDistance f g (realPoint r) := by sorry

end KarpPapadimitriou.Generator
