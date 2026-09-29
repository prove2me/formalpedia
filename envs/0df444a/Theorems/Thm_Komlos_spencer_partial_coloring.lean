-- Prove2me | Theorems.Thm_Komlos_spencer_partial_coloring
-- name    : Komlos.spencer_partial_coloring
-- status  : Proved
-- author  : @Hartmann_Psi
-- created : 2026-09-08T23:45:42.250349+00:00
-- url     : https://prove2.me/theorems/ee3618ab-30fe-46a3-9265-55ad91852073
-- title:
--   Partial colouring step for $n$ sets on $n$ points
-- statement:
--   Let $A$ be an $n\times n$ matrix with entries in $\{0,1\}$, let $T$ be a nonempty set of columns, and let $0<\theta\le 1/2$ and $\nu\ge 2$ satisfy the budget inequality
--
--   $$n\cdot 2e^{-\nu^{2}/2}\Bigl(\tfrac{3}{4}\nu^{2}+2\Bigr)\;\le\;\tfrac{2}{3}\,\theta^{2}\,|T| .$$
--
--   Then there is a **partial colouring** $\chi\in\{-1,0,+1\}^{n}$, vanishing outside $T$, which colours at least a $(1-\theta)$ fraction of $T$,
--
--   $$\#\{j\in T: \chi_j\neq 0\}\;\ge\;(1-\theta)|T| ,$$
--
--   and keeps every row balanced to within $\nu\sqrt{|T|}$:
--
--   $$\Bigl|\sum_{j\in T}A_{ij}\chi_j\Bigr|\;\le\;\nu\sqrt{|T|}\qquad\text{for every }i .$$
--
--   This is the step that the partial colouring method of Beck and Spencer iterates: one colours a constant fraction of the remaining points at a time, at a cost that shrinks geometrically, instead of colouring everything at once. The two parameters trade against each other — a smaller $\theta$ colours more points per application but demands a larger $\nu$ — and the budget inequality is exactly the constraint linking them. The quantity on its left is a closed form in $\nu$; on the right, the constant $2/3$ is a safely sub-critical stand-in for $1/(2\ln 2)$.
--
--   **Formalization Note** Partial colourings are encoded as real-valued vectors taking the three values $1,-1,0$, with $0$ marking an uncoloured coordinate; the requirement that $\chi$ vanish outside $T$ makes the restriction to the active set explicit. Both conclusions are stated for the sum over $T$ only, so the statement composes directly with itself when it is applied again to the uncoloured part.
-- source:
--   J. Spencer, Six standard deviations suffice, Trans. Amer. Math. Soc. 289 (1985) 679-706, Theorem 1 and Section 2 (the entropy / partial colouring method), https://doi.org/10.1090/S0002-9947-1985-0784009-0

import Mathlib
open Finset

namespace Komlos

theorem spencer_partial_coloring
    (n : ℕ) (A : Fin n → Fin n → ℝ) (h01 : ∀ i j, A i j = 0 ∨ A i j = 1)
    (T : Finset (Fin n)) (hT : 0 < T.card)
    (θ ν : ℝ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1 / 2) (hν : 2 ≤ ν)
    (hbudget : (n : ℝ) * (2 * Real.exp (-(ν ^ 2) / 2) * (3 * ν ^ 2 / 4 + 2))
        ≤ (2 / 3) * θ ^ 2 * (T.card : ℝ)) :
    ∃ χ : Fin n → ℝ,
      (∀ j, χ j = 1 ∨ χ j = -1 ∨ χ j = 0) ∧
      (∀ j, j ∉ T → χ j = 0) ∧
      (1 - θ) * (T.card : ℝ) ≤ ((T.filter (fun j => χ j ≠ 0)).card : ℝ) ∧
      (∀ i, |∑ j ∈ T, A i j * χ j| ≤ ν * Real.sqrt (T.card : ℝ)) := by sorry

end Komlos
