-- Prove2me | Theorems.Thm_OpenPitMIP_Extraction_theorem_3
-- name    : OpenPitMIP.Extraction.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:44:28.483977+00:00
-- url     : https://prove2.me/theorems/d89c0e26-b0c0-4e9b-a4c8-039644855e26
-- title:
--   Theorem 3, p. 1433 — diamond cuts: w_{c₂,t₂} ≤ w_{c₁,t₁} when the diamond cl(c₂) ∩ rcl(c₁) outweighs Q_{t₁,t₂}
-- statement:
--   Consider an instance of the PCPSP-C satisfying the standing assumptions. Let $t_1,t_2\in\mathcal T$ with $t_1\le t_2$, let $Q_{t_1,t_2}=\sum_{t'=t_1}^{t_2}U_{t'}$, and let $c_1,c_2\in\mathcal C$ with $c_1\prec c_2$. Then:
--
--   1. if $q(cl(c_2)\cap rcl(c_1))>Q_{t_1,t_2}$, the inequality
--   $$w_{c_2,t_2}\le w_{c_1,t_1}$$
--   holds at every point feasible for the PCPSP-F that satisfies the mining capacity rows (8);
--   2. if $q\bigl((cl(c_2)\cap rcl(c_1))\setminus\{c_1,c_2\}\bigr)>Q_{t_1,t_2}$, the same inequality holds at every point feasible for the PCPSP-P that satisfies (8).
--
--   The set $cl(c_2)\cap rcl(c_1)$ consists of the clusters lying between $c_1$ and $c_2$ in the precedence order; the cut says that if this set is too heavy to mine within periods $t_1$ to $t_2$, then $c_2$ cannot be started by $t_2$ unless $c_1$ was already started by $t_1$.
--
--   **Formalization Note** The page writes $cl(c_2)\cap rcl(c_1)\setminus\{c_1,c_2\}$; its proof reads it as $(cl(c_2)\cap rcl(c_1))\setminus\{c_1,c_2\}$, which is the grouping used. $Q_{t_1,t_2}$ includes period $t_1$, as on the page. Validity is stated as for Theorem 2.
-- source:
--   Oper. Res. 68(5), Theorem 3, p. 1433

import Mathlib
import Definitions.Def_OpenPitMIP_Extraction_Setting

namespace OpenPitMIP.Extraction

/-- Theorem 3 (diamond cuts), p. 1433. For periods `t₁ ≤ t₂` and clusters `c₁ ≺ c₂`: if
`q(cl(c₂) ∩ rcl(c₁)) > Q_{t₁,t₂}`, then `w_{c₂,t₂} ≤ w_{c₁,t₁}` is valid for the PCPSP-F; if
`q((cl(c₂) ∩ rcl(c₁)) \ {c₁, c₂}) > Q_{t₁,t₂}`, it is valid for the PCPSP-P. "Valid" means: at
every feasible point whose mining capacity rows (8) hold. -/
theorem theorem_3 {B D C : Type} [Fintype B] [Fintype D] [Fintype C] [DecidableEq C] {T m : ℕ}
    (I : PCPSPC B D C T m) (hI : I.Standing) (t₁ t₂ : Fin T) (ht : t₁ ≤ t₂) (c₁ c₂ : C)
    (hc : I.cprec c₁ c₂) :
    (I.Qint t₁ t₂ < I.qSet (I.cl c₂ ∩ I.rcl c₁) →
      ∀ (x : C → Fin T → ℝ) (y : B → D → Fin T → ℝ),
        I.Feasible .F x y → I.MiningCap y → PCPSPC.cum x c₂ t₂ ≤ PCPSPC.cum x c₁ t₁) ∧
    (I.Qint t₁ t₂ < I.qSet ((I.cl c₂ ∩ I.rcl c₁) \ {c₁, c₂}) →
      ∀ (x : C → Fin T → ℝ) (y : B → D → Fin T → ℝ),
        I.Feasible .P x y → I.MiningCap y → PCPSPC.cum x c₂ t₂ ≤ PCPSPC.cum x c₁ t₁) := by sorry

end OpenPitMIP.Extraction
