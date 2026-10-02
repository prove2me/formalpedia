-- Prove2me | Theorems.Thm_MDPFinance_Stationary_structure_theorem_stationary
-- name    : MDPFinance.Stationary.structure_theorem_stationary
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T21:46:37.563346+00:00
-- url     : https://prove2.me/theorems/7c679470-49d7-4b74-9014-023cf1adf0c3
-- title:
--   Theorem 2.5.4 — the stationary structure theorem
-- statement:
--   Let (SAN) hold for $(\mathrm{I\!M}, \Delta)$. Then, for $0 \leq n \leq N$: $J_n \in
--   \mathrm{I\!M}$; for $1 \leq n \leq N$, $J_n = T J_{n-1}$; and $J_n = T^n g$. Moreover, for
--   $n = 1,\dots,N$ there is a maximizer $f_n^* \in \Delta$ of $J_{n-1}$, and any such family
--   assembles (via $\pi(k) := f^*_{N-k}$ for $k=0,\dots,N-1$) into a policy attaining $J_N$.
--
--   **Formalization Note.** The "every sequence of maximizers defines an optimal policy" clause
--   is formalized as: the existence of one maximizer family $f^*_1,\dots,f^*_N$ whose associated
--   policy $\pi(k) := f^*_{N-k}$ attains $J_N$ exactly — a faithful, if index-heavy, translation
--   of the Forward Induction Algorithm's output into a usable $N$-stage policy.
--
--   **Formalization Note (moderation).** Part (b) is stated as the book does: maximizers
--   $f_n^*\in\Delta$ of $J_{n-1}$ exist for every $n$, and *every* sequence of maximizers defines
--   an optimal policy $(f_N^*,\dots,f_1^*)$ (a universally quantified statement), not merely the
--   existence of one such family. (AN) is carried as `hAN`.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 41, PDF 56, Theorem 2.5.4

import Mathlib
import Definitions.Def_MDPFinance_Stationary_Model
import Definitions.Def_MDPFinance_Stationary_Policy
import Definitions.Def_MDPFinance_Stationary_Operators
import Definitions.Def_MDPFinance_Stationary_StructureAssumption
import Definitions.Def_MDPFinance_Stationary_ValueFunction

open MeasureTheory ProbabilityTheory

namespace MDPFinance.Stationary

/-- Theorem 2.5.4 (Structure Theorem) (Bäuerle–Rieder, p. 41, PDF 56), under the standing
Integrability Assumption (AN). Let (SAN) be satisfied.
a) Then `J_n ∈ IM` and the Bellman equation `J_n = T J_{n-1}` holds for `1 ≤ n ≤ N`, i.e.
`J_0 = g`, `J_n(x) = sup_{a ∈ D(x)} [r(x,a) + β ∫ J_{n-1}(x') Q(dx'|x,a)]`. Moreover, `J_n = T^n
g`. b) For `n = 1, …, N` there exist maximizers `f_n^*` of `J_{n-1}` with `f_n^* ∈ Δ`, and every
sequence of maximizers `f_n^*` of `J_{n-1}` defines an optimal policy `(f_N^*, …, f_1^*)` for
the stationary `N`-stage Markov Decision Model: for every such sequence, the policy `π(k) := f^*_{N-k}` for
`k = 0, …, N-1` attains `J_N`. -/
theorem structure_theorem_stationary {E A : Type*} [MeasurableSpace E] [MeasurableSpace A]
    (M : StationaryMarkovDecisionModel E A) (IMs : Set (E → EReal)) (Delta : Set (E → A))
    (hSAN : StructureAssumption M IMs Delta) (N : ℕ) (hAN : IntegrabilityAssumption M N) :
    (∀ n ≤ N, J M n ∈ IMs) ∧
      (∀ n, 1 ≤ n → n ≤ N → J M n = T M (J M (n - 1))) ∧
      (∀ n ≤ N, J M n = TChain M n (fun x => (M.g x : EReal))) ∧
      (∀ n, 1 ≤ n → n ≤ N → ∃ f ∈ Delta, IsMaximizer M (J M (n - 1)) f) ∧
      (∀ fstar : ℕ → E → A, (∀ n, 1 ≤ n → n ≤ N → IsMaximizer M (J M (n - 1)) (fstar n)) →
        Jpi M (fun k => fstar (N - k)) N = J M N) := by sorry

end MDPFinance.Stationary
