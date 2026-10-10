-- Prove2me | Theorems.Thm_OpenPitMIP_UltPit_feasible_nested_pits
-- name    : OpenPitMIP.UltPit.feasible_nested_pits
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T12:42:50.223644+00:00
-- url     : https://prove2.me/theorems/4df24ddc-eca3-475c-a5f7-c505cb5e0e37
-- title:
--   §2.2, p. 1428 — feasible PCPSP-C solutions correspond to a nested sequence of pits
-- statement:
--   Consider an instance of the PCPSP-C (formulation (1)–(7)) under the standing assumptions of §2.1, and let $(x, y)$ be a feasible solution under either integrality condition (10) or (11). For each period $t \in \mathcal T$ define
--   $$\mathcal B(x; t) = \Big\{ b \in \mathcal B : \sum_{t'=1}^{t} x_{c(b),t'} > 0 \Big\}.$$
--   Then:
--   1. for every $t$, the set $\mathcal B(x; t)$ is a pit: if $b_1 \prec b_2$ and $b_2 \in \mathcal B(x;t)$ then $b_1 \in \mathcal B(x;t)$;
--   2. the sets are nested: $t \le t'$ implies $\mathcal B(x; t) \subseteq \mathcal B(x; t')$.
--
--   This is the observation that links PCPSP-C schedules with the phase design problem: a schedule extracts, period by period, an increasing family of pits.
--
--   **Formalization Note** The precedence constraints (4) are imposed only along the arcs $\mathcal A$ of the transitive reduction, as in the paper. Periods are `Fin T` (index $t$ is period $t+1$).
-- source:
--   Oper. Res. 68(5), §2.2, p. 1428

import Mathlib
import Definitions.Def_OpenPitMIP_UltPit_Setting

namespace OpenPitMIP.UltPit

open PCPSPC

/-- §2.2, p. 1428: for every feasible solution of the PCPSP-C and every period `t`, the set
`𝓑(x; t) = {b ∈ 𝓑 : ∑_{t'=1}^{t} x_{c(b),t'} > 0}` is a pit, and these sets are nested in `t`. -/
theorem feasible_nested_pits {B D C : Type} [Fintype B] [Fintype D] [Fintype C] {T m : ℕ}
    (I : PCPSPC B D C T m) (hI : I.Standing) (κ : Integrality)
    (x : C → Fin T → ℝ) (y : B → D → Fin T → ℝ) (hxy : I.Feasible κ x y) :
    (∀ t, I.IsPit {b | 0 < cum x (I.clu b) t}) ∧
      ∀ t t', t ≤ t' → {b | 0 < cum x (I.clu b) t} ⊆ {b | 0 < cum x (I.clu b) t'} := by sorry

end OpenPitMIP.UltPit
