-- Prove2me | Theorems.Thm_HoffmanBound_ErrorBound_lemma3
-- name    : HoffmanBound.ErrorBound.lemma3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T09:36:44.610401+00:00
-- url     : https://prove2.me/theorems/140da91a-d131-46cb-83cc-38b0e1685f70
-- title:
--   Lemma 3 — on the set E there is d_S > 0 with Fₘ((Mx)⁺) ≧ d_S Fₙ(x)
-- statement:
--   Let $F_n$ and $F_m$ be positive homogeneous functions in the sense of (3). Let $S$ be a set of rows of $A$, let $M$ be the $m\times n$ matrix obtained from $A$ by substituting $0$ for the rows not in $S$, let $\Omega_0=\{z : Mz\le 0\}$, and let $E$ be the set of all $x$ such that (i) $x\notin\Omega_0$ and (ii) the origin is the point of $\Omega_0$ nearest to $x$. Then there exists $d_S>0$ such that
--   $$
--   F_m\bigl((Mx)^+\bigr)\ge d_S\,F_n(x)\qquad\text{for every } x\in E.
--   $$
--
--   The constant $d_S$ is chosen before $x$; together with Lemma 2 it gives the main theorem with $c=e/\min_S d_S$.
--
--   **Formalization Note** $S$ is an arbitrary `Finset` of row indices (including $\emptyset$ and all rows), and $M$ keeps all $m$ rows, with zeros in the rows outside $S$.
-- source:
--   Hoffman, On Approximate Solutions of Systems of Linear Inequalities, J. Res. Nat. Bur. Standards 49 (1952), p. 263 (PDF p. 1), Lemma 3

import Mathlib
import Definitions.Def_HoffmanBound_ErrorBound_Model

namespace HoffmanBound.ErrorBound

open Matrix

/-- Hoffman 1952, p. 263, Lemma 3. Let `M` be obtained from `A` by substituting `0` for the rows
not in `S`, `Ω = {z | M z ≤ 0}`, and `E` the set of `x ∉ Ω` whose nearest point in `Ω` is the
origin. For `F_n`, `F_m` satisfying (3) there is `d_S > 0` with `F_m((M x)⁺) ≥ d_S F_n(x)` for all
`x ∈ E`. -/
theorem lemma3 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (S : Finset (Fin m))
    (Fn : (Fin n → ℝ) → ℝ) (Fm : (Fin m → ℝ) → ℝ)
    (hFn : IsPosHomogeneous Fn) (hFm : IsPosHomogeneous Fm) :
    ∃ dS : ℝ, 0 < dS ∧ ∀ x ∈ setE A S, dS * Fn x ≤ Fm (posPartVec (rowsOn A S *ᵥ x)) := by sorry

end HoffmanBound.ErrorBound
