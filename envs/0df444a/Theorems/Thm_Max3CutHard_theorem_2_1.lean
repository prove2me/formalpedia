-- Prove2me | Theorems.Thm_Max3CutHard_theorem_2_1
-- name    : Max3CutHard.theorem_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:48:03.684205+00:00
-- url     : https://prove2.me/theorems/c5ca5bc5-5452-437c-b01f-e2fd225c0266
-- title:
--   Theorem 2.1 — Håstad: gap $1-\varepsilon$ vs. $1/3+\varepsilon$ for balanced 3Lin($\mathbb Z_3$)
-- statement:
--   **Theorem 2.1 (Håstad).** For every $\varepsilon>0$ it is NP-hard, given a balanced role-separated instance $\Phi$ of 3Lin($\mathbb Z_3$), to distinguish
--
--   $$\mathrm{val}(\Phi)\ge1-\varepsilon\qquad\text{from}\qquad \mathrm{val}(\Phi)\le\tfrac13+\varepsilon.$$
--
--   Here an instance is a list of $m$ equations $u_e+w_e+w'_e=t_e$ ($u_e\in U$, $w_e\ne w'_e\in W$, $U$ and $W$ disjoint), each of weight $1/m$, written in unary. "NP-hard to distinguish" means: every NP language reduces in polynomial time to the promise problem, members going to instances of value at least $1-\varepsilon$ and non-members to instances of value at most $1/3+\varepsilon$.
--
--   This is the starting point of the reduction; the source cites it from Håstad (2001, Thm. 5.9 with Lemmas 5.10–5.11), with tests on the same folded class discarded and the types balanced.
--
--   Differences from the source:
--   - reading: instances with weights λ_e ≥ 0 summing to 1 → a list of m equations, each of weight 1/m (repetitions give rational weights), encoded in unary by encLin; reason: the source does not fix an input format; for fixed ε Håstad's verifier has finitely many tests with rational probabilities, and hardness on this subclass is the stronger reading
--   - reading: it is NP-hard to distinguish → SetCoverThreshold.SetCover.GapNPHard (Karp-style promise NP-hardness); reason: the standard meaning of NP-hardness of a gap problem
--   - encoding: disjoint U, W; distinct w_e, w′_e → types Fin nU and Fin nW; the field hne; reason: Lean convention; same instances
-- source:
--   Ni, Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k, arXiv:2611.01402, Theorem 2.1, p.4

import Mathlib
import Definitions.Def_SetCoverThreshold_SetCover_Complexity
import Definitions.Def_Max3CutHard_encLin
import Definitions.Def_Max3CutHard_LinInst_toWInst
import Definitions.Def_Max3CutHard_WInst_val
import Definitions.Def_Max3CutHard_WInst_Balanced

namespace Max3CutHard

/-- **Theorem 2.1 (Håstad [Hås01]).** Ni, *Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k*, arXiv:2611.01402, Theorem 2.1, p.4: "For every `ε > 0` it is NP-hard,
given a balanced role-separated instance `Φ` of 3Lin(ℤ₃), to distinguish `val(Φ) ≥ 1 − ε` from
`val(Φ) ≤ 1/3 + ε`."

**Formalization Note.** Instances are `LinInst` (a list of equations, each of weight `1/m`),
encoded by `encLin` (unary numbers, injective). Role separation and `w_e ≠ w′_e` are built into
the type. NP-hardness is the published Karp-style `GapNPHard`. `Balanced` already forces at least
one equation. -/
theorem theorem_2_1 : ∀ ε : ℝ, 0 < ε →
    SetCoverThreshold.SetCover.GapNPHard encLin
      (fun Φ : LinInst => Φ.toWInst.Balanced ∧ 1 - ε ≤ Φ.toWInst.val)
      (fun Φ : LinInst => Φ.toWInst.Balanced ∧ Φ.toWInst.val ≤ 1 / 3 + ε) := by sorry

end Max3CutHard
