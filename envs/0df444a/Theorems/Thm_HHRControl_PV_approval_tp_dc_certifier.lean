-- Prove2me | Theorems.Thm_HHRControl_PV_approval_tp_dc_certifier
-- name    : HHRControl.PV.approval_tp_dc_certifier
-- status  : Open
-- author  : @martelus trismortuus
-- created : 2026-11-18T06:14:17.338093+00:00
-- url     : https://prove2.me/theorems/12e3fb87-56d2-4598-8455-eb78b68cbdf7
-- title:
--   Polynomial-time certifier for destructive control by partition of voters, approval (TP)
-- statement:
--   Let $C=\{0,\dots,m-1\}$ be the candidates, $c\in C$ the distinguished candidate and $V$ a list of $n$ voters. Each voter casts an approval ballot $A_v\subseteq C$; write $a(x)$ for the number of voters approving $x$. Say that $(C,c,V)$ satisfies the *approval-TP dethroning criterion* if either $a(c)\le a(x)$ for some $x\ne c$, or there are $y,z\ne c$ with
--
--   $$\#\{v : c\in A_v,\ y,z\notin A_v\}+2\;\le\;\#\{v : c\notin A_v,\ y\in A_v\text{ or }z\in A_v\},$$
--
--   $\#\{v: c\notin A_v,\ y\in A_v\}\ge1$ and $\#\{v: c\notin A_v,\ z\in A_v\}\ge1$.
--
--   By the reduction submitted for Theorem 4.21, this holds exactly when $c$ can be made not the unique winner by partition of voters in model TP (ties promote). The second alternative is a partition in which $y$ strictly beats $c$ in one part and $z$ strictly beats $c$ in the other, so that no subcommittee nominates $c$.
--
--   **Claim.** There is a polynomial-time computable function $f$ on instance codes such that: if $(C,c,V)$ satisfies the criterion, $f$ outputs the code of a partition $(V_1,V\setminus V_1)$ under which $c$ is not the unique winner of the two-stage election; otherwise $f$ outputs the code of "control impossible". (The partitions in the proof of the reduction are explicit: each part collects all voters of one type plus a prescribed number of voters of another type.)
-- source:
--   Hemaspaandra, Hemaspaandra & Rothe, Anyone but Him: The Complexity of Precluding an Alternative, Artificial Intelligence 171 (2007), arXiv:cs/0507027v5, p. 19 and Appendix A (pp. 34-36), proof of Theorem 4.21 (model TP)

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_HHRControl_PV_Elections
import Definitions.Def_HHRControl_PV_Languages

namespace HHRControl.PV

open CookPvsNP ProjSchedTW.Complexity Finset

/-- The certifying algorithm behind destructive control by partition of voters for approval voting in model TP (Theorem 4.21, p. 19, corrected in Appendix A, pp. 34–36)
(Hemaspaandra–Hemaspaandra–Rothe): a polynomial-time function maps the code of every election
satisfying the dethroning criterion to the code of a partition of the voters under which `c` is not
the unique two-stage winner, and every other election code to "control impossible". -/
theorem approval_tp_dc_certifier :
    ∃ f : List BSym → List BSym, PolyTimeComputable f ∧
      ∀ (m n : ℕ) (c : Fin m) (P : Fin n → Approval m),
        (((∃ x : Fin m, x ≠ c ∧ approvalScore P univ c ≤ approvalScore P univ x) ∨
          ∃ y z : Fin m, y ≠ c ∧ z ≠ c ∧
            (univ.filter fun v => c ∈ P v ∧ y ∉ P v ∧ z ∉ P v).card + 2 ≤
              (univ.filter fun v => c ∉ P v ∧ (y ∈ P v ∨ z ∈ P v)).card ∧
            1 ≤ (univ.filter fun v => c ∉ P v ∧ y ∈ P v).card ∧
            1 ≤ (univ.filter fun v => c ∉ P v ∧ z ∈ P v).card) →
          ∃ V₁ : Finset (Fin n), twoStage .TP approval P V₁ ≠ {c} ∧
            f (electionCode approval c P) = partitionCode V₁) ∧
        (¬ ((∃ x : Fin m, x ≠ c ∧ approvalScore P univ c ≤ approvalScore P univ x) ∨
          ∃ y z : Fin m, y ≠ c ∧ z ≠ c ∧
            (univ.filter fun v => c ∈ P v ∧ y ∉ P v ∧ z ∉ P v).card + 2 ≤
              (univ.filter fun v => c ∉ P v ∧ (y ∈ P v ∨ z ∈ P v)).card ∧
            1 ≤ (univ.filter fun v => c ∉ P v ∧ y ∈ P v).card ∧
            1 ≤ (univ.filter fun v => c ∉ P v ∧ z ∈ P v).card) →
          f (electionCode approval c P) = impossibleCode) := by sorry

end HHRControl.PV
