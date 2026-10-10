-- Prove2me | Theorems.Thm_OpenPitMIP_Extraction_eq_18_20
-- name    : OpenPitMIP.Extraction.eq_18_20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:43:20.066002+00:00
-- url     : https://prove2.me/theorems/959035ef-0989-4a33-bf06-c00effa2a253
-- title:
--   (18)–(20), p. 1432 — the cumulative variables w are monotone in t, respect the arcs, and satisfy the capacity knapsack
-- statement:
--   Consider an instance of the PCPSP-C satisfying the standing assumptions, and let $(x,y)$ be feasible for it (under either integrality condition) and satisfy the mining capacity rows (8). Let $w_{c,t}=\sum_{t'=1}^{t}x_{c,t'}$ and $q_c=\sum_{b\in c}q_b$. Then
--   $$w_{c,t}\le w_{c,t+1}\quad(c\in\mathcal C,\ t=1,\dots,T-1),\tag{18}$$
--   $$w_{c,t}\le w_{c',t}\quad((c,c')\in\mathcal A,\ t\in\mathcal T),\tag{19}$$
--   $$\sum_{c\in\mathcal C}q_c\,w_{c,t}\le\sum_{t'=1}^{t}U_{t'}\quad(t\in\mathcal T).\tag{20}$$
--
--   Together, (18)–(20) form the precedence-constrained knapsack relaxation of the PCPSP-C from which all extraction cuts are derived.
--
--   **Formalization Note** The paper says (4) and (8) imply these; (18) in fact uses $x\ge 0$, which follows from (2), (6) and the nonemptiness of every cluster (the clusters partition $\mathcal B$). (19) restates (4). Periods are `Fin T` (index $t$ is period $t+1$), so (18) is stated for $t+1<T$.
-- source:
--   Oper. Res. 68(5), §5, (18)–(20), p. 1432

import Mathlib
import Definitions.Def_OpenPitMIP_Extraction_Setting

namespace OpenPitMIP.Extraction

/-- Displays (18)–(20), §5, p. 1432: at every feasible point of the PCPSP-C (either integrality
condition) whose mining capacity rows (8) hold, the cumulative variables `w = cum x` are
nondecreasing in time (18), respect the immediate precedences (19), and satisfy the aggregated
capacity knapsack (20) with `q_c = q({c})`. Index `t : Fin T` is period `t + 1`. -/
theorem eq_18_20 {B D C : Type} [Fintype B] [Fintype D] [Fintype C] {T m : ℕ}
    (I : PCPSPC B D C T m) (hI : I.Standing) (κ : OpenPitMIP.UltPit.Integrality)
    (x : C → Fin T → ℝ) (y : B → D → Fin T → ℝ)
    (hxy : I.Feasible κ x y) (hcap : I.MiningCap y) :
    (∀ (c : C) (t : Fin T) (h : t.val + 1 < T),
        PCPSPC.cum x c t ≤ PCPSPC.cum x c ⟨t.val + 1, h⟩) ∧
    (∀ c c' : C, I.arc c c' → ∀ t : Fin T, PCPSPC.cum x c t ≤ PCPSPC.cum x c' t) ∧
    (∀ t : Fin T, ∑ c, I.qSet {c} * PCPSPC.cum x c t ≤ ∑ t' ∈ Finset.Iic t, I.U t') := by sorry

end OpenPitMIP.Extraction
