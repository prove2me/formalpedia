-- Prove2me | Theorems.Thm_MeanCertificates1424_Hardness_Supplement_proposition_B_1
-- name    : MeanCertificates1424.Hardness.Supplement.proposition_B_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T09:08:59.58223+00:00
-- url     : https://prove2.me/theorems/af05c399-dc93-4bdc-a453-17a420b93b5c
-- title:
--   Proposition B.1 — detection as a hitting game
-- statement:
--   A detector audits at most $q\in\{0,\dots,n\}$ coordinates exactly, possibly adaptively and with private randomness, and must never raise an alarm when $x=y$; the actual field $x$ and the report $y$ are fixed before the randomness. For a known class $\mathcal H$ of fields let $S_b(y)=\{\operatorname{supp}(x-y):x\in\mathcal H,0<\|x-y\|_0\le b\}$. If $S_b(y)\ne\emptyset$, the optimal worst-case miss probability is
--   $$\beta_q(y)=\min_{\pi\in\Delta(\{Q\subseteq V:|Q|\le q\})}\ \max_{S\in S_b(y)}\ \Pr_{Q\sim\pi}(Q\cap S=\emptyset),$$
--   and it is $0$ if there are no alternatives. Adaptivity does not improve this value, and the smallest number of audits for deterministic detection with zero miss probability is the minimum hitting-set size of $S_b(y)$.
--
--   **Formalization Note** The optimal value is the infimum over randomized adaptive detectors; the statement includes that the minimum over $\pi$ is attained and that some detector attains the optimal value.
--
--   Differences from the source:
--   - generalization: the report y ∈ H_L(G) is a legitimate field (Appendix B standing assumption) → y is any real vector; reason: the proof uses only that an alternative agrees with y off its support; this specializes to legitimate y
--   - encoding: randomized detectors → probability mass functions over deterministic adaptive strategies; reason: private randomness drawn before the run; finite distributions are included
-- source:
--   chaomeng chen, Junhao Dong, STOC 2027 submission #1424 (October 2026), Proposition B.1, printed p.24 (PDF p.26)

import Mathlib
import Definitions.Def_MeanCertificates1424_Hardness_Supplement_Detection

set_option autoImplicit false

open MeanCertificates1424.Hardness

namespace MeanCertificates1424.Hardness.Supplement

/-- Proposition B.1, printed p.24 / PDF p.26. For any known class `H` of real fields,
`S_b(y) = {supp(x − y) : x ∈ H, 0 < ‖x − y‖₀ ≤ b}`, and `q ≤ n` audits: if `S_b(y) ≠ ∅`, the
optimal worst-case miss probability over randomized adaptive detectors with no false alarm
equals `min_{π ∈ Δ({Q : |Q| ≤ q})} max_{S ∈ S_b(y)} Pr_{Q∼π}(Q ∩ S = ∅)` (the minimum is
attained, and some detector is optimal); it is `0` with no alternatives; adaptivity does not
improve it (it equals the nonadaptive value); and the least number of audits of a deterministic
detector with zero miss probability is the minimum hitting-set size of `S_b(y)`. -/
theorem proposition_B_1 {n : ℕ} (H : Set (Fin n → ℝ)) (b q : ℕ) (y : Fin n → ℝ) (hq : q ≤ n) :
    ((supportFamily H b y).Nonempty →
      (∃ π₀ : PMF (Finset (Fin n)), AuditDist q π₀ ∧
        optMiss q y (altOf H b y) = ⨆ S ∈ supportFamily H b y, avoidProb π₀ S ∧
        ∀ π : PMF (Finset (Fin n)), AuditDist q π →
          (⨆ S ∈ supportFamily H b y, avoidProb π₀ S) ≤ ⨆ S ∈ supportFamily H b y, avoidProb π S) ∧
      ∃ π : Policy n, NoFalseAlarm π q y ∧
        (⨆ x ∈ altOf H b y, missProb π q x) = optMiss q y (altOf H b y)) ∧
    (supportFamily H b y = ∅ → optMiss q y (altOf H b y) = 0) ∧
    detAudits y (altOf H b y) = minHitting (supportFamily H b y) := by sorry

end MeanCertificates1424.Hardness.Supplement
