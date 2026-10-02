-- Prove2me | Theorems.Thm_MDPFinance_POMDP_theorem_5_3_3
-- name    : MDPFinance.POMDP.theorem_5_3_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T22:15:52.991898+00:00
-- url     : https://prove2.me/theorems/8875c5b4-7768-45dc-a7c5-aa7be507e940
-- title:
--   Theorem 5.3.3 — Bellman equation for the filtered model and the optimal POMDP policy [GOAL]
-- statement:
--   Suppose the filtered Markov Decision Model satisfies the Structure Assumption of
--   Theorem 2.3.8. a) Then $J_0'(x,\rho) = g'(x,\rho)$, and for $1\le n\le N$,
--   $$J_n'(x,\rho) = \sup_{a\in D(x)}\Big[r'(x,\rho,a) + \beta\int J_{n-1}'(x',\rho')\,
--   Q'(d(x',\rho')\mid x,\rho,a)\Big].$$
--   b) If $f_n'$ is a maximizer of $J_{n-1}'$ for $n=1,\dots,N$, then $\pi^*:=(f_0^*,\dots,
--   f_{N-1}^*)$, $f_n^*(h_n):=f_{N-n}'(x_n,\mu_n(\cdot\mid h_n))$, is optimal for the $N$-stage
--   Partially Observable Markov Decision Problem.
--
--   This is the chapter's central reduction and the goal of this mission: a Partially Observable
--   Markov Decision Process cannot be attacked by Chapter 2's theory directly, because admissible
--   policies see only the observable history while the state includes an unobservable component —
--   but once the unobservable state is replaced by its posterior $\rho$ (Theorem 5.3.2's filtered
--   model), the resulting problem *is* an ordinary Markov Decision Model, to which Theorem 2.3.8
--   applies unchanged, turning a genuinely new problem class into an instance of already-developed
--   theory.
--
--   **Formalization Note.** The Structure Assumption is restated locally as `SatisfiesSAN`
--   (existential classes $IM_n,\Delta_n$ with the three defining clauses of Definition 2.4.2),
--   matching hard rule 3's requirement to declare shared machinery locally rather than import chunk
--   `02a`'s copy. Part b)'s reindexing $f_n^*(h_n):=f_{N-n}'(x_n,\mu_n(\cdot\mid h_n))$ (a
--   maximizer for the "$N{-}n$ stages-to-go" value function, evaluated at absolute time $n$) mirrors
--   the same stages-to-go/absolute-time reindexing pattern already established in chunks `02d`/`04b`.
--   A formalization that solved (a) by first assuming the *conclusion* (that `Jprime` already
--   satisfies the recursion) would trivialize the theorem; here `Jprime` is independently defined via
--   a `sup` over admissible policies (`Def_MDPFinance_POMDP_FilteredModel`), so part (a) is a genuine
--   claim about that `sup`, not a restatement of its own definition.
--
--   **Moderation note.** The section's Integrability Assumption (`hInt`, equivalent to (AN) for the filtered model, p. 158) is a hypothesis, as Theorem 2.3.8 requires. Part b) is stated for *every* choice of measurable feasible maximizers $f'_1,\dots,f'_N$ of $J'_0,\dots,J'_{N-1}$ (the draft only asserted that *some* choice yields an optimal policy), together with the existence of such maximizers. The Structure Assumption's classes $IM_n$ are classes of $[-\infty,\infty]$-valued functions, matching the value functions.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 158, PDF 172, Theorem 5.3.3

import Mathlib
import Definitions.Def_MDPFinance_POMDP_Model
import Definitions.Def_MDPFinance_POMDP_Policy
import Definitions.Def_MDPFinance_POMDP_Objective
import Definitions.Def_MDPFinance_POMDP_FilterData
import Definitions.Def_MDPFinance_POMDP_FilteredModel

open MeasureTheory ProbabilityTheory

namespace MDPFinance.POMDP

variable {EX EY A : Type*} [MeasurableSpace EX] [MeasurableSpace EY] [MeasurableSpace A]

/-- The Structure Assumption (SAN) of Theorem 2.3.8, restated locally for the filtered model
(Bäuerle–Rieder, Definition 2.4.2/Theorem 2.3.8, cited at p. 158, PDF 172; not imported from
chunk `02a` per hard rule 3): classes `IM_n` of value functions and `Δ_n` of decision rules with
(i) `g' ∈ IM_N`; (ii) `v ∈ IM_{n+1} ⟹ T'_n v ∈ IM_n`; (iii) every `v ∈ IM_{n+1}` has a maximizer
of `T'_n v` in `Δ_n`. -/
def FilteredModel.SatisfiesSAN (M : PartiallyObservableMDM EX EY A) (Fd : FilterData M)
    (M' : FilteredModel M Fd) (N : ℕ) : Prop :=
  ∃ (IM : ℕ → Set (EX × ProbabilityMeasure EY → EReal))
    (Δ : ℕ → Set (EX × ProbabilityMeasure EY → A)),
    FilteredModel.gprime M ∈ IM N ∧
      (∀ n < N, ∀ v ∈ IM (n + 1), (fun e => FilteredModel.Tprime M Fd M' v e) ∈ IM n) ∧
      ∀ n < N, ∀ v ∈ IM (n + 1), ∃ f ∈ Δ n, Measurable f ∧
        ∀ e : EX × ProbabilityMeasure EY, f e ∈ M.Dx e.1 ∧
          FilteredModel.rprime M e (f e) +
              (M.β : EReal) * erealIntegral (M'.Qprime (e, f e)) v =
            FilteredModel.Tprime M Fd M' v e

/-- Theorem 5.3.3 (Bäuerle–Rieder, p. 158, PDF 172) — the goal of this mission. Suppose the
filtered Markov Decision Model satisfies the Structure Assumption of Theorem 2.3.8. a) Then the
Bellman equation holds: `J'_0(x,ρ) = g'(x,ρ)`, and for `1 ≤ n ≤ N`, `J'_n(x,ρ) = sup_{a ∈ D(x)}
[r'(x,ρ,a) + β ∫ J'_{n-1}(x',ρ') Q'(d(x',ρ')|x,ρ,a)]`. b) Let `f'_n` be a maximizer of `J'_{n-1}`
for `n = 1,…,N`. Then `π^* := (f^*_0,…,f^*_{N-1})`, `f^*_n(h_n) := f'_{N-n}(x_n,μ_n(·|h_n))`, is
optimal for the `N`-stage Partially Observable Markov Decision Problem. Values are in
`[-∞,∞]` under the section's standing Integrability Assumption (p. 151, equivalent to (AN) for
the filtered model, p. 158). Part b) is stated for *every* choice of maximizers `f'_1,…,f'_N`
(with `f'_n` a measurable, feasible maximizer of `J'_{n-1}`), together with the existence of
such maximizers that Theorem 2.3.8 provides. -/
theorem theorem_5_3_3 [Nonempty A] (M : PartiallyObservableMDM EX EY A) (Fd : FilterData M)
    (M' : FilteredModel M Fd) (N : ℕ) (hInt : M.IntegrabilityAssumption N)
    (hSAN : FilteredModel.SatisfiesSAN M Fd M' N) :
    (∀ x ρ, FilteredModel.Jprime M Fd M' 0 x ρ = FilteredModel.gprime M (x, ρ)) ∧
      (∀ n, 1 ≤ n → n ≤ N → ∀ (x : EX) (ρ : ProbabilityMeasure EY),
        FilteredModel.Jprime M Fd M' n x ρ =
          ⨆ a ∈ M.Dx x, FilteredModel.rprime M (x, ρ) a +
            (M.β : EReal) * erealIntegral (M'.Qprime ((x, ρ), a))
              (fun e' => FilteredModel.Jprime M Fd M' (n - 1) e'.1 e'.2)) ∧
      (∃ fprime : ℕ → EX × ProbabilityMeasure EY → A,
        ∀ n, 1 ≤ n → n ≤ N → Measurable (fprime n) ∧
          ∀ e : EX × ProbabilityMeasure EY, fprime n e ∈ M.Dx e.1 ∧
            FilteredModel.rprime M e (fprime n e) +
                (M.β : EReal) * erealIntegral (M'.Qprime (e, fprime n e))
                  (fun e' => FilteredModel.Jprime M Fd M' (n - 1) e'.1 e'.2) =
              FilteredModel.Jprime M Fd M' n e.1 e.2) ∧
      (∀ fprime : ℕ → EX × ProbabilityMeasure EY → A,
        (∀ n, 1 ≤ n → n ≤ N → Measurable (fprime n) ∧
          ∀ e : EX × ProbabilityMeasure EY, fprime n e ∈ M.Dx e.1 ∧
            FilteredModel.rprime M e (fprime n e) +
                (M.β : EReal) * erealIntegral (M'.Qprime (e, fprime n e))
                  (fun e' => FilteredModel.Jprime M Fd M' (n - 1) e'.1 e'.2) =
              FilteredModel.Jprime M Fd M' n e.1 e.2) →
        M.IsPolicy N (fun n xs as => fprime (N - n) (xs n, Fd.mu M n xs as)) ∧
          ∀ x0 : EX, M.JNpi (fun n xs as => fprime (N - n) (xs n, Fd.mu M n xs as)) N x0 =
            M.JN N x0) := by sorry

end MDPFinance.POMDP
