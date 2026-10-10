-- Prove2me | Theorems.Thm_OpenPitMIP_UltPit_dominated_triplet
-- name    : OpenPitMIP.UltPit.dominated_triplet
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T12:42:31.021478+00:00
-- url     : https://prove2.me/theorems/11f5ca3e-4153-4bbb-a88e-1a5554d670af
-- title:
--   §4.2, p. 1431 — a dominated triplet (b, d₂, t) can be set to zero in some optimal solution
-- statement:
--   Consider an instance of the PCPSP-C with either integrality condition, a block $b$, two distinct destinations $d_1 \ne d_2$ and a period $t$. Write $G_{b,d,t}$ for the column of $G$ that multiplies $y_{b,d,t}$. Suppose the triplet $(b, d_1, t)$ **dominates** $(b, d_2, t)$:
--   $$G_{b,d_1,t} \le G_{b,d_2,t} \ \text{(componentwise)} \qquad\text{and}\qquad p_{b,d_1,t} \ge p_{b,d_2,t}.$$
--   If the PCPSP-C has an optimal solution, then it has an optimal solution $(x, y)$ with $y_{b,d_2,t} = 0$.
--
--   This justifies the dominated-triplet preprocessing: the variable $y_{b,d_2,t}$ can be removed from the model without changing the optimal value.
--
--   **Formalization Note** The comparison is between the discounted values $p_{b,d,t} = p_{b,d}/(1+r)^t$, as on the page. The hypothesis $d_1 \ne d_2$ is implicit in "dominates" (with $d_1 = d_2$ every triplet would dominate itself, and the conclusion would be false in general).
-- source:
--   Oper. Res. 68(5), §4.2, p. 1431

import Mathlib
import Definitions.Def_OpenPitMIP_UltPit_Setting

namespace OpenPitMIP.UltPit

open PCPSPC

/-- §4.2, p. 1431: if the triplet `(b, d₁, t)` dominates `(b, d₂, t)` — the column `G_{b,d₁,t}`
is componentwise at most `G_{b,d₂,t}` and `p_{b,d₁,t} ≥ p_{b,d₂,t}` — then, whenever the
PCPSP-C has an optimal solution, it has one with `y_{b,d₂,t} = 0`. -/
theorem dominated_triplet {B D C : Type} [Fintype B] [Fintype D] [Fintype C] {T m : ℕ}
    (I : PCPSPC B D C T m) (κ : Integrality) (b : B) (d₁ d₂ : D) (hd : d₁ ≠ d₂) (t : Fin T)
    (hG : ∀ i, I.G i b d₁ t ≤ I.G i b d₂ t) (hp : I.value b d₁ t ≥ I.value b d₂ t)
    (hopt : ∃ x y, I.Optimal κ x y) :
    ∃ x y, I.Optimal κ x y ∧ y b d₂ t = 0 := by sorry

end OpenPitMIP.UltPit
