-- Prove2me | Theorems.Thm_MDPFinance_Bellman_structure_theorem
-- name    : MDPFinance.Bellman.structure_theorem
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-09-27T20:16:42.641004+00:00
-- url     : https://prove2.me/theorems/51d43a09-ba69-435e-939c-c11b042fa7d8
-- title:
--   Theorem 2.3.8 — the Structure Theorem
-- statement:
--   This is the book's central finite-horizon result. Suppose the Structure Assumption (SAN) holds
--   for some choice of $(\mathrm{IM}_n)$, $(\Delta_n)$. Then:
--
--   $$
--   V_n \in \mathrm{IM}_n \ \text{ for every } n,\qquad
--   V_N = g_N,\qquad
--   V_n(x) = \sup_{a \in D_n(x)}\left[r_n(x,a) + \int V_{n+1}(x')\, Q_n(dx'\mid x,a)\right]
--   \ (n < N),
--   $$
--
--   so that $(V_n)$ satisfies the Bellman equation and, unrolled, $V_n = T_n T_{n+1} \cdots
--   T_{N-1} g_N$. Moreover, for every $n = 0,\dots,N-1$ there exists a maximizer $f_n$ of $V_{n+1}$
--   with $f_n \in \Delta_n$, and **every** sequence of maximizers $(f_0^*,\dots,f_{N-1}^*)$ of
--   $(V_1,\dots,V_N)$ defines an optimal policy for the $N$-stage Markov Decision Problem.
--
--   The content is twofold: the recursive (Bellman) characterization of the value function $V_n$
--   itself — defined a priori as a supremum over *all* $N$-stage policies, an object with no
--   obvious recursive structure — and the existence of a genuinely optimal, Markov (state-feedback)
--   policy, built one stage at a time from measurable maximizers, under one abstract structural
--   hypothesis rather than a case-by-case compactness argument. This generalizes the finite-state
--   discounted and stochastic-shortest-path Bellman equations (e.g. as covered for finite state and
--   action spaces in the `BertsekasDP` mission series) to general Borel state and action spaces:
--   there, the supremum defining $T_n v(x)$ is trivially attained because $D_n(x)$ is finite; here,
--   (SAN) is exactly the abstract substitute that makes the supremum attained and measurably
--   selectable without any finiteness or compactness assumption on $E$ or $A$ built into the
--   statement itself.
--
--   **Formalization Note.** $V_n$ is the value function of `MDPFinance.Bellman.V` — a supremum over
--   *all* policies, fixed independently of this theorem — not an object merely postulated to solve
--   the Bellman equation (that weaker claim is Theorem 2.3.7, `verification_theorem`); stating the
--   goal this way is essential; the alternative would trivialize the theorem into a restatement of
--   Theorem 2.3.7 under an unused hypothesis. "Every sequence of maximizers is optimal" is formalized
--   as a universally quantified implication over an arbitrary policy `fstar` satisfying the
--   maximizer condition at every stage, matching the book's "every sequence... defines an optimal
--   policy" exactly.
--
--   **Formalization Note (moderation).** The Integrability Assumption (AN) of Section 2.2, which
--   the book assumes throughout, is carried as the explicit hypothesis `hAN`; without it the
--   expectations defining $V_n^\pi$ need not exist, and the extended-real integral's convention
--   for $\infty - \infty$ would make the statement's terms artefacts of that convention.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 23, Theorem 2.3.8

import Mathlib
import Definitions.Def_MDPFinance_Bellman_Model
import Definitions.Def_MDPFinance_Bellman_Policy
import Definitions.Def_MDPFinance_Bellman_Operators
import Definitions.Def_MDPFinance_Bellman_ValueFunction
import Definitions.Def_MDPFinance_Bellman_StructureAssumption

open MeasureTheory ProbabilityTheory MDPFinance.Bellman

namespace MDPFinance.Bellman

/-- Theorem 2.3.8 (Structure Theorem; Bäuerle–Rieder, p. 23, PDF 38), the book's central
finite-horizon result, under the standing Integrability Assumption (AN). Let the Structure
Assumption (SAN) be satisfied by `(IM_n)`, `(Δ_n)`.
Then: a) `V_n ∈ IM_n` and `(V_n)` satisfies the Bellman equation, i.e. `V_N = g_N` and
`V_n(x) = sup_{a ∈ D_n(x)} [r_n(x,a) + ∫ V_{n+1}(x') Q_n(dx'|x,a)]` for `n = 0,…,N-1`;
b) `V_n = T_n T_{n+1} ⋯ T_{N-1} g_N`; c) for `n = 0,…,N-1` there exists a maximizer `f_n` of
`V_{n+1}` with `f_n ∈ Δ_n`, and every sequence of maximizers `f_n^*` of `V_{n+1}` defines an
optimal policy `(f_0^*,…,f_{N-1}^*)` for the `N`-stage Markov Decision Problem. Here `V_n` is
*the* value function `sup_π V_n^π` fixed before this theorem is proved (Def., p. 18, PDF 33),
not an arbitrary object merely postulated to satisfy the Bellman equation — that weaker claim
is Theorem 2.3.7. -/
theorem structure_theorem {E A : Type*} [MeasurableSpace E] [MeasurableSpace A] {N : ℕ}
    (M : MarkovDecisionModel E A N) (hAN : IntegrabilityAssumption M)
    (IMs : ℕ → Set (E → EReal)) (Deltas : ℕ → Set (E → A))
    (hSAN : StructureAssumption M IMs Deltas) :
    (∀ n ≤ N, V M n ∈ IMs n) ∧
    (V M N = fun x => (M.g x : EReal)) ∧
    (∀ n < N, ∀ x, V M n x = ⨆ a ∈ M.Dx n x, (M.r n (x, a) : EReal) + erealIntegral
        (M.Q n (x, a)) (V M (n + 1))) ∧
    (∀ n ≤ N, V M n = TChain M (N - n) n (fun x => (M.g x : EReal))) ∧
    (∀ n < N, ∃ f ∈ Deltas n, IsMaximizer M n (V M (n + 1)) f) ∧
    (∀ fstar : Policy M, (∀ n < N, IsMaximizer M n (V M (n + 1)) (fstar.1 n)) →
        Vpi M fstar 0 = V M 0) := by sorry

end MDPFinance.Bellman
