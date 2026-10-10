-- Prove2me | Theorems.Thm_OpenPitMIP_Vrhs_eq_29_30
-- name    : OpenPitMIP.Vrhs.eq_29_30
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:43:25.649446+00:00
-- url     : https://prove2.me/theorems/ddffd60d-5562-4e74-9985-808c291f04d1
-- title:
--   (29)–(30), p. 1434 — for both integrality conditions, w_{c,t} < 1 forces y = 0 on rcl(c) \ {c}, and y_{b,d,t} ≤ w_{c(b),t}
-- statement:
--   Consider an instance of the PCPSP-C satisfying the standing assumptions, and let $(x,y)$ be feasible for it under either the full integrality condition (10) or the partial integrality condition (11). Write $w_{c,t}=\sum_{t'=1}^{t}x_{c,t'}$ for the cumulative extraction of cluster $c$ by period $t$. Then
--
--   1. for every cluster $c$, every block $b$ with $c(b)\in rcl(c)\setminus\{c\}$, every destination $d$ and every period $t$,
--   $$w_{c,t}<1\ \Longrightarrow\ y_{b,d,t}=0;\tag{29}$$
--   2. for every block $b$, destination $d$ and period $t$,
--   $$y_{b,d,t}\le w_{c(b),t}.\tag{30}$$
--
--   Condition (29) says that a block of a strict successor of $c$ cannot be sent anywhere before $c$ is fully extracted; (30) bounds the fraction of a block sent to one destination in one period by the cumulative extraction of its cluster. Together with the destination capacity rows (9) they are the conditions from which the VRHS cuts of Theorem 7 are derived.
--
--   **Formalization Note** The third condition (31) of the page is the destination capacity row (9) itself; it is a hypothesis wherever it is used, not a statement. Condition (29) fails for the linear relaxation, so the statement quantifies over both integrality conditions, not over fractional points.
-- source:
--   Oper. Res. 68(5), §5.2.2, (29)–(30), p. 1434

import Mathlib
import Definitions.Def_OpenPitMIP_Vrhs_Setting

namespace OpenPitMIP.Vrhs

open PCPSPC

/-- (29)–(30), Oper. Res. 68(5), §5.2.2, p. 1434: for both full and partial integrality, every
feasible `(x, y)` of the PCPSP-C satisfies (29) `w_{c,t} < 1 ⇒ y_{b,d,t} = 0` for every block `b`
of a cluster in `rcl(c) \ {c}`, and (30) `y_{b,d,t} ≤ w_{c(b),t}`. -/
theorem eq_29_30 {B D C : Type} [Fintype B] [Fintype D] [Fintype C] [DecidableEq C] {T m : ℕ}
    (I : PCPSPC B D C T m) (hI : I.Standing) (κ : OpenPitMIP.UltPit.Integrality)
    (x : C → Fin T → ℝ) (y : B → D → Fin T → ℝ) (hxy : I.Feasible κ x y) :
    (∀ (c : C) (b : B) (d : D) (t : Fin T),
      I.clu b ∈ I.rcl c \ {c} → cum x c t < 1 → y b d t = 0) ∧
    (∀ (b : B) (d : D) (t : Fin T), y b d t ≤ cum x (I.clu b) t) := by sorry

end OpenPitMIP.Vrhs
