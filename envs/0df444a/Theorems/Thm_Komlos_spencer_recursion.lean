-- Prove2me | Theorems.Thm_Komlos_spencer_recursion
-- name    : Komlos.spencer_recursion
-- status  : Proved
-- author  : @Hartmann_Psi
-- created : 2026-09-08T23:46:07.106741+00:00
-- url     : https://prove2.me/theorems/5fd30e4f-df84-48ab-bc08-cc37ab695aa4
-- title:
--   Spencer's bound from the partial colouring step and the residual colouring
-- statement:
--   Assume both of the following.
--
--   1. **(Partial colouring step.)** For every $0/1$ matrix, every nonempty active set $T$ of columns and all parameters $0<\theta\le 1/2$, $\nu\ge2$ obeying $n\cdot 2e^{-\nu^{2}/2}(\tfrac34\nu^{2}+2)\le\tfrac{2}{3}\theta^{2}|T|$, there is a partial colouring of $T$ leaving at most a $\theta$ fraction of $T$ uncoloured whose row sums are at most $\nu\sqrt{|T|}$ in absolute value.
--   2. **(Residual colouring.)** Every set $T$ of columns carries a $\pm1$ colouring whose row sums are at most $\sqrt{2|T|\log(4n)}$ in absolute value.
--
--   Then every $n\times n$ matrix with entries in $\{0,1\}$ admits signs $\varepsilon_j\in\{\pm1\}$ with
--
--   $$\Bigl|\sum_{j=1}^{n}A_{ij}\varepsilon_j\Bigr|\;\le\;6\sqrt{n}\qquad\text{for every }i,$$
--
--   which is Spencer's theorem. What has to be supplied is the scheduling: the fraction colored at each application, the parameter $\nu$ used there, the point at which the recursion is stopped in favour of the residual colouring, and the verification that the resulting geometric series of costs stays below $6$. The constant $6$ is the one from the original paper, and it is what makes the schedule delicate: a random colouring alone gives $\Theta(\sqrt{n\log n})$, and the recursion has to pay for every round.
--
--   **Formalization Note** The two inputs appear as explicit hypotheses so that this statement is exactly the combinatorial bookkeeping of the argument and nothing else; they are the separately stated partial colouring and residual colouring problems. Colourings are encoded as real-valued vectors, with $0$ marking an uncoloured coordinate in the partial colourings.
-- source:
--   J. Spencer, Six standard deviations suffice, Trans. Amer. Math. Soc. 289 (1985) 679-706, Theorem 1 and Section 2 (the entropy / partial colouring method), https://doi.org/10.1090/S0002-9947-1985-0784009-0

import Mathlib
import Definitions.Def_Komlos_model
open Finset

namespace Komlos

theorem spencer_recursion
    (pcl : ∀ (n : ℕ) (A : Fin n → Fin n → ℝ), (∀ i j, A i j = 0 ∨ A i j = 1) →
      ∀ (T : Finset (Fin n)), 0 < T.card → ∀ θ ν : ℝ, 0 < θ → θ ≤ 1 / 2 → 2 ≤ ν →
        (n : ℝ) * (2 * Real.exp (-(ν ^ 2) / 2) * (3 * ν ^ 2 / 4 + 2))
            ≤ (2 / 3) * θ ^ 2 * (T.card : ℝ) →
        ∃ χ : Fin n → ℝ,
          (∀ j, χ j = 1 ∨ χ j = -1 ∨ χ j = 0) ∧
          (∀ j, j ∉ T → χ j = 0) ∧
          (1 - θ) * (T.card : ℝ) ≤ ((T.filter (fun j => χ j ≠ 0)).card : ℝ) ∧
          (∀ i, |∑ j ∈ T, A i j * χ j| ≤ ν * Real.sqrt (T.card : ℝ)))
    (fin : ∀ (n : ℕ), 0 < n → ∀ (A : Fin n → Fin n → ℝ), (∀ i j, A i j = 0 ∨ A i j = 1) →
      ∀ (T : Finset (Fin n)),
        ∃ χ : Fin n → ℝ,
          (∀ j, j ∈ T → (χ j = 1 ∨ χ j = -1)) ∧
          (∀ j, j ∉ T → χ j = 0) ∧
          (∀ i, |∑ j ∈ T, A i j * χ j|
              ≤ Real.sqrt (2 * (T.card : ℝ) * Real.log (4 * n))))
    (n : ℕ) (A : Fin n → Fin n → ℝ) (h01 : ∀ i j, A i j = 0 ∨ A i j = 1) :
    ∃ ε : Fin n → ℝ, IsSignVector ε ∧
      ∀ i, |∑ j, A i j * ε j| ≤ 6 * Real.sqrt n := by sorry

end Komlos
