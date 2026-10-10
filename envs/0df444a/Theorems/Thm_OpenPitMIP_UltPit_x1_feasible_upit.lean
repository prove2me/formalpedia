-- Prove2me | Theorems.Thm_OpenPitMIP_UltPit_x1_feasible_upit
-- name    : OpenPitMIP.UltPit.x1_feasible_upit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T12:42:29.790643+00:00
-- url     : https://prove2.me/theorems/1048a680-f0a3-4e1c-ad5c-976dc0f3878d
-- title:
--   §4.1, p. 1431 — the total extraction x¹ of a feasible PCPSP-C solution is feasible for U-PIT
-- statement:
--   Consider an instance of the PCPSP-C under the standing assumptions of §2.1 and a feasible solution $(x, y)$ under either integrality condition. Define, for each cluster $c$,
--   $$x^1_c = \sum_{t \in \mathcal T} x_{c,t}.$$
--   Then $x^1$ is feasible for the ultimate pit limit problem U-PIT: $x^1_c \le x^1_{c'}$ for every arc $(c, c') \in \mathcal A$, and $0 \le x^1_c \le 1$ for every cluster $c$.
--
--   This is what makes the pit limit $P^{OPT}$ of a PCPSP-C solution, the support of $x^1$, comparable with the pit limit of U-PIT in Theorem 1.
--
--   **Formalization Note** The paper states this for a minimal optimal solution $(x^*, y^*)$ and justifies it by constraints (4) alone; the statement here assumes only feasibility, which is stronger. The bound $x^1_c \ge 0$ uses that every cluster contains a block (standing assumption), so that $x_{c,t} = \sum_d y_{b,d,t} \ge 0$.
-- source:
--   Oper. Res. 68(5), §4.1, p. 1431

import Mathlib
import Definitions.Def_OpenPitMIP_UltPit_Setting

namespace OpenPitMIP.UltPit

open PCPSPC

/-- §4.1, p. 1431: for a feasible solution `(x, y)` of the PCPSP-C, the vector
`x¹_c = ∑_{t ∈ 𝒯} x_{c,t}` is feasible for U-PIT (12)–(14). -/
theorem x1_feasible_upit {B D C : Type} [Fintype B] [Fintype D] [Fintype C] {T m : ℕ}
    (I : PCPSPC B D C T m) (hI : I.Standing) (κ : Integrality)
    (x : C → Fin T → ℝ) (y : B → D → Fin T → ℝ) (hxy : I.Feasible κ x y) :
    I.UPitFeasible (fun c => ∑ t, x c t) := by sorry

end OpenPitMIP.UltPit
