-- Prove2me | Theorems.Thm_HHRControl_PV_plurality_te_dc_certifier
-- name    : HHRControl.PV.plurality_te_dc_certifier
-- status  : Open
-- author  : @martelus trismortuus
-- created : 2026-11-18T06:13:33.930196+00:00
-- url     : https://prove2.me/theorems/748a14cc-9a1f-4605-81e2-95f6d9b4b8d5
-- title:
--   Polynomial-time certifier for destructive control by partition of voters, plurality (TE)
-- statement:
--   Let $C=\{0,\dots,m-1\}$ be the candidates, $c\in C$ the distinguished candidate and $V$ a list of $n$ voters. Each voter casts a strict ranking; write $s(x)$ for the number of voters ranking $x$ first, and $N(x>y)$ for the number of voters preferring $x$ to $y$. Say that $(C,c,V)$ satisfies the *plurality-TE dethroning criterion* if one of the following holds:
--
--   1. $s(c)\le s(y)$ for some $y\ne c$ ($c$ is not the unique plurality winner);
--   2. $s(c)\le s(y)+s(z)$ for some distinct $y,z\ne c$ (the paper's inequality (4.1));
--   3. some $x\ne c$ has $s(c)\ge1$, $s(x)\ge1$, $N(c>x)\le N(x>c)$, and $s(t)+2\le s(c)+s(x)$ for every $t\notin\{c,x\}$.
--
--   By the reduction submitted for Theorem 4.19, the criterion holds exactly when $c$ can be made not the unique winner by partition of voters in model TE (ties eliminate). Alternatives 1 and 2 are the partitions in which neither subcommittee nominates $c$; alternative 3 is the partition in which one subcommittee nominates $c$ and the other a candidate $x$ that ties or beats $c$ in the run-off. **Note.** The paper states the third condition with a strict inequality, $\mathrm{score}(e)<\mathrm{score}(c)+\mathrm{score}(d)-2$. Its own construction needs only $\le$ (the $V_2$ count $s(e)-\min(s(c)-1,s(e))$ must be below $s(x)$), and the strict form is not necessary, so the criterion here uses $\le$.
--
--   **Claim.** There is a polynomial-time computable function $f$ on instance codes such that: if $(C,c,V)$ satisfies the criterion, $f$ outputs the code of a partition $(V_1,V\setminus V_1)$ under which $c$ is not the unique winner of the two-stage election; otherwise $f$ outputs the code of "control impossible". (The partitions in the proof of the reduction are explicit: each part collects all voters of one type plus a prescribed number of voters of another type.)
-- source:
--   Hemaspaandra, Hemaspaandra & Rothe, Anyone but Him: The Complexity of Precluding an Alternative, Artificial Intelligence 171 (2007), arXiv:cs/0507027v5, p. 17, proof of Theorem 4.19 (inequality (4.1) and the three conditions on d)

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_HHRControl_PV_Elections
import Definitions.Def_HHRControl_PV_Languages

namespace HHRControl.PV

open CookPvsNP ProjSchedTW.Complexity Finset

/-- The certifying algorithm behind destructive control by partition of voters for plurality voting in model TE (Theorem 4.19, p. 17)
(Hemaspaandra–Hemaspaandra–Rothe): a polynomial-time function maps the code of every election
satisfying the dethroning criterion to the code of a partition of the voters under which `c` is not
the unique two-stage winner, and every other election code to "control impossible". -/
theorem plurality_te_dc_certifier :
    ∃ f : List BSym → List BSym, PolyTimeComputable f ∧
      ∀ (m n : ℕ) (c : Fin m) (P : Fin n → Ranking m),
        (((∃ y, y ≠ c ∧ pluralityScore P univ univ c ≤ pluralityScore P univ univ y) ∨
          (∃ y z, y ≠ c ∧ z ≠ c ∧ y ≠ z ∧
            pluralityScore P univ univ c ≤
              pluralityScore P univ univ y + pluralityScore P univ univ z) ∨
          (∃ x, x ≠ c ∧ 1 ≤ pluralityScore P univ univ c ∧ 1 ≤ pluralityScore P univ univ x ∧
            prefCount P univ c x ≤ prefCount P univ x c ∧
            ∀ t, t ≠ c → t ≠ x →
              pluralityScore P univ univ t + 2 ≤
                pluralityScore P univ univ c + pluralityScore P univ univ x)) →
          ∃ V₁ : Finset (Fin n), twoStage .TE plurality P V₁ ≠ {c} ∧
            f (electionCode plurality c P) = partitionCode V₁) ∧
        (¬ ((∃ y, y ≠ c ∧ pluralityScore P univ univ c ≤ pluralityScore P univ univ y) ∨
          (∃ y z, y ≠ c ∧ z ≠ c ∧ y ≠ z ∧
            pluralityScore P univ univ c ≤
              pluralityScore P univ univ y + pluralityScore P univ univ z) ∨
          (∃ x, x ≠ c ∧ 1 ≤ pluralityScore P univ univ c ∧ 1 ≤ pluralityScore P univ univ x ∧
            prefCount P univ c x ≤ prefCount P univ x c ∧
            ∀ t, t ≠ c → t ≠ x →
              pluralityScore P univ univ t + 2 ≤
                pluralityScore P univ univ c + pluralityScore P univ univ x)) →
          f (electionCode plurality c P) = impossibleCode) := by sorry

end HHRControl.PV
