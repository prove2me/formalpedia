-- Prove2me | Theorems.Thm_OctalGames_periodicity_theorem
-- name    : OctalGames.periodicity_theorem
-- status  : Proved
-- author  : @martelus trismortuus
-- created : 2026-11-18T17:49:53.376193+00:00
-- url     : https://prove2.me/theorems/602c7790-3622-4acf-83ae-26ac7bdc44b1
-- title:
--   Octal Periodicity Theorem
-- statement:
--   Let $\Gamma=d_0.d_1d_2\cdots$ be an octal game whose digits vanish beyond index $k$ (so $\Gamma$ has finite length at most $k$), and let $\mathcal G(n)$ be the nim-value of a $\Gamma$-heap of $n$ tokens (see the definition `OctalGames_Code`). Let $n_0\ge 1$ and $p\ge 1$. If
--
--   $$
--   \mathcal G(n+p)=\mathcal G(n)\qquad\text{for all } n \text{ with } n_0\le n<2n_0+p+k,
--   $$
--
--   then $\mathcal G(n+p)=\mathcal G(n)$ for all $n\ge n_0$. That is, $\Gamma$ is periodic with period $p$ and preperiod $n_0$.
--
--   This is the Octal Periodicity Theorem. It reduces periodicity of a finite octal game to a finite computation: one computes $\mathcal G(0),\dots,\mathcal G(2n_0+2p+k-1)$ and checks the hypothesis. For example, Kayles ($0.77$) has period $12$ and preperiod $71$, which follows from the first $2\cdot71+2\cdot12+2=168$ values. It is the standard tool behind every known solution of a periodic octal game, and a companion to the open question `OctalGames.guy_question` (is every finite octal game eventually periodic?).
--
--   **Formalization Note** Siegel states the theorem for the exact length $k$ (the largest index with $d_k\neq0$). Here $k$ is any index beyond which all digits vanish; the two forms are equivalent, since a larger $k$ only enlarges the range that the hypothesis checks.
-- source:
--   A. N. Siegel, Combinatorial Game Theory, Graduate Studies in Mathematics 146, AMS 2013, Section IV.2, p. 190, Theorem 2.7 (Octal Periodicity Theorem); worked examples p. 191 (Dawson's Kayles 2*53+2*34+2=176, Kayles 2*71+2*12+2=168). Originally Guy-Smith 1956.

import Mathlib
import Definitions.Def_OctalGames_Code
open OctalGames

theorem OctalGames.periodicity_theorem (c : Code) (k n₀ p : ℕ) (hk : ∀ i, k < i → c.digit i = 0) (hn₀ : 1 ≤ n₀) (hp : 1 ≤ p) (h : ∀ n, n₀ ≤ n → n < 2 * n₀ + p + k → grundy c (n + p) = grundy c n) : ∀ n, n₀ ≤ n → grundy c (n + p) = grundy c n := by sorry
