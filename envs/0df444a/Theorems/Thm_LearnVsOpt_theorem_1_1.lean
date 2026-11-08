-- Prove2me | Theorems.Thm_LearnVsOpt_theorem_1_1
-- name    : LearnVsOpt.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:08:02.126235+00:00
-- url     : https://prove2.me/theorems/b401b8f6-0c2f-4d06-81f8-54d31bfa675b
-- title:
--   Theorem 1.1 (Theorems 6.7 and 7.2) — one efficient budget-feasible learner: non-manipulable, budgeted or not, with low interval stochastic regret
-- statement:
--   There are absolute constants $C>0$ and $a,d\in\mathbb N$ such that the following holds for every repeated budgeted game with $n_O,n_L$ actions, every $\rho_L\in(0,1]$ with a learner's null action $j_0$ and a row of the optimizer inducing the zero vector, and every horizon $T\ge1$, for Algorithm 1 run with the forecaster of Algorithm 2.
--
--   1. **Budget.** For every valid tie-breaking rule, every adaptive optimizer, every outcome and every $t\le T$, $\sum_{r\le t}C_L[i_r,j_r]\le t\rho_L$.
--   2. **Non-manipulability.** For every valid tie-breaking rule and every adaptive optimizer,
--   $$
--   \mathbb E\Big[\sum_{t=1}^TU_O[i_t,j_t]\Big]\le\mathrm{BSE}\cdot T+C\Big(\sqrt{n_O}\,n_L+\frac{\sqrt{n_L}}{\rho_L}\Big)\big(\sqrt T+\hat n_O\big).
--   $$
--   3. **Budgeted optimizer.** For every $\rho_O\in(0,1]$ such that the optimizer has an action of zero cost, every valid tie-breaking rule and every adaptive optimizer with $\mathbb E[\sum_tC_O[i_t,j_t]]\le\rho_OT$,
--   $$
--   \mathbb E\Big[\sum_{t=1}^TU_O[i_t,j_t]\Big]\le\mathrm{BSE}_2\cdot T+\frac{C}{\rho_O}\Big(\sqrt{n_O}\,n_L+\frac{\sqrt{n_L}}{\rho_L}\Big)\big(\sqrt T+\hat n_O\big),
--   $$
--   with $\mathrm{BSE}_2$ the two-phase value (26).
--   4. **Low interval stochastic regret.** For every valid tie-breaking rule, if $[T]$ is partitioned into $S\ge1$ contiguous intervals $I_s$ in which the optimizer draws $i_t\sim x^{(s)}$ independently, then on every interval and for every $y^\star_s\in\mathrm{BR}_L(x^{(s)})$,
--   $$
--   \mathbb E\Big[\sum_{t\in I_s}U_L[i_t,j_t]\Big]\ge|I_s|\cdot\big(x^{(s)}\big)^\top U_Ly_s^\star-C\,\frac{\sqrt{Sn_LT}}{\rho_L}.
--   $$
--   5. **Running time.** The concrete selector `vertexSel` is valid, and with it, for every adaptive optimizer, on every outcome and in every round, the learner charges at most $a(T+n_L)^d$ unit operations on the unit-cost real RAM.
--
--   This answers the paper's central question: there is an efficient learning algorithm that, in every repeated budgeted game, is non-manipulable and has low interval stochastic regret. The optimizer's and the learner's guarantees are simultaneous, and the learner needs no prior knowledge of the game.
--
--   Differences from the source:
--   - encoding: T rounds; rounds t = 1, …, T; actions [n_O], [n_L]; forecasts in Δ_{n̂}; the iterates of F_t; expectations → T ≥ 1, Outcome lists with round t at position t − 1, actions Fin nO, Fin nL, forecasts ℕ → ℝ vanishing past the dictionary, F_t as the list of M_t iterates, expect as a finite-support tsum; reason: Lean representation of the same objects
--   - encoding: R_t, L_t, Z_t as sums of expected errors → read from the state of the program of Algorithms 1 and 2: atoms (k, j₁, j₂, w, q) for R_t and 2√n_L·L_t for L_t; reason: the program stores the same sums; the theorems speak about the program's own Z_t
--   - encoding: δ(f, k), k an index of 𝒰𝒞 → δ(f, v), v = uc^(k) the realized vector; the indicator 1_{k=k'} reads D[k'] = v; reason: same object for a dictionary without repeats; also defined for a vector not yet observed
--   - encoding: each player has a null action of cost 0 (§2, p.6), with the all-zeros vector uc^(1) = 0 ∈ 𝒰𝒞 (p.16) → j₀ with C_L[i, j₀] = 0 for all i, and hzero: some row i has U_L[i, ·] = C_L[i, ·] = 0; reason: the paper's standing assumptions, as hypotheses
--   - reading: Algorithm 1 indents "Observe … report it to the forecaster" under the active branch (p.7) → the dictionary is updated in every round, and Z_t only in active rounds; reason: §2, p.6 assumes full-information feedback, p.16 defines 𝒰𝒞_t by the vectors observed in rounds 1, …, t, and the proofs of Claim 6.6 and Lemma 6.2 need exactly this
--   - generalization: an adaptive optimizer whose i_t is chosen against the learner → a kernel σ from the full past (i_r, m_r, j_r), r < t, including the learner's realized forecast indices, to PMF (Fin n_O); reason: every optimizer that sees less is an instance; moves within a round stay simultaneous
--   - generalization: any consistent tie-breaking rule, with J⃗ = (j, j) and Q = 0 for a pure best response (p.8) → every selector valid on (u, c) ∈ [0, 1]^{2n_L} with c[j₀] = 0; the only condition on J⃗ is j₁ = j₂ → Q = 0, so a pair j₁ ≠ j₂ with Q ∈ {0, 1} is also allowed; reason: the paper's rule is a valid selector, and its arguments use no more than validity
--   - generalization: ρ_L ∈ (0, 1] with ρ_L = Ω(1) w.r.t. T (§2, p.6) → any ρ_L ∈ (0, 1], with no relation to T; reason: the bounds are explicit in ρ_L; a constant ρ_L is an instance
--   - generalization: one null action of the optimizer with the zero row of p.16 and zero cost (§2, p.6; §7, p.22) → separate existentials: hzero for the learner's row, and for the budgeted clause ∃ i, C_O[i, ·] = 0, with possibly different actions; reason: a single null action satisfies both
--   - generalization: the optimizer's total cost is at most ρ_O T on the path (§2, p.6) → E[Σ_t C_O[i_t, j_t]] ≤ ρ_O T; reason: a pathwise budget implies it, and the Lagrangian step needs only the expectation
--   - encoding: [T] partitioned into S ≥ 1 contiguous intervals I_s with i_t ∼ x^(s) in each → IsPiecewiseStationary: I s = Ioc a b, pairwise disjoint, with union Icc 1 T; (σ past i).toReal = x s i for all pasts of length t − 1, t ∈ I s; empty intervals allowed; reason: same objects; an empty interval carries no constraint
--   - encoding: max in (2), (26), (27); both (2) and (26) are named BSE → sSup of the set of values, named BSE and BSE₂; reason: the sets are nonempty and bounded under the null actions; attainment is not a claim of the theorem
--   - reading: Theorem 6.7 is "our main theorem" (pp.18, 21) → one statement of Theorems 6.7 and 7.2 together; reason: the abstract claims "any adaptive optimizer, budgeted or not", and Theorem 1.1 is the informal version of both
--   - reading: O(·) in Theorem 6.7 → an absolute constant C chosen before n_O, n_L, the game and T, positive, with a separate statement for each parameter displayed; reason: Theorem 6.7 displays every parameter; Theorem 1.1's "polynomial factors" is its informal, weaker version
--   - reading: "runs in time poly(T, n_L)" (per round, Theorem 1.1) → on every outcome and round, the units the learner charges on the unit-cost real RAM are at most a(T + n_L)^d, with absolute a, d, for the concrete selector vertexSel, which is valid; reason: entries are real numbers, so a bit model is undefined on the stated instances, and the paper's proof counts iterations and a linear program in n_L variables (p.22); the machine has only + − × / min max, comparisons and array and loop bookkeeping
--   - reading: "never runs out of budget" → Σ_{r≤t} C_L[i_r, j_r] ≤ tρ_L for every round t and every outcome; reason: the proof on p.22 shows this; it implies the total budget at t = T
-- source:
--   Fikioris, Sivan & Tardos, Learning vs. Optimizing Players in Budgeted Games, arXiv:2611.05580, Theorem 1.1, p.2; Theorem 6.7, p.21; Theorem 7.2, p.23

import Mathlib
import Definitions.Def_LearnVsOpt_BSE
import Definitions.Def_LearnVsOpt_Play

open scoped Matrix

namespace LearnVsOpt

/-- **Formal Theorem 1.1: Theorems 6.7 and 7.2 together** (Fikioris, Sivan & Tardos, *Learning vs.
Optimizing Players in Budgeted Games*, arXiv:2611.05580, Theorem 1.1, p.2; Theorem 6.7, p.21;
Theorem 7.2, p.23). There is one learning algorithm, Algorithm 1 with the forecaster of Algorithm 2,
that in every repeated budgeted game: (a) never exceeds its budget; (b) is non-manipulable by any
adaptive optimizer, `E[Σ_t U_O[i_t, j_t]] ≤ BSE · T + O((√n_O n_L + √n_L/ρ_L)(√T + n̂_O))`; (c) against a
budgeted optimizer has the same bound relative to the two-phase value (26), with an additional factor
`1/ρ_O` in the error; (d) has low interval stochastic regret,
`E[Σ_{t∈I_s} U_L[i_t, j_t]] ≥ |I_s| · (x^(s))⊤U_L y⋆_s − O(√(S n_L T)/ρ_L)`; (e) runs in `poly(T, n_L)` time
per round.

**Formalization Note.** `O(·)` is an absolute constant `C`, and the polynomial's `a`, `d` are absolute,
all chosen before the game. Clauses (a)–(d) hold for every valid tie-breaking rule; (e) is for the
concrete selector `vertexSel`, on the unit-cost real RAM. The optimizer in (c) respects its budget in
expectation, which a pathwise budget implies. -/
theorem theorem_1_1 :
    ∃ C : ℝ, 0 < C ∧ ∃ a d : ℕ, ∀ {nO nL : ℕ} (G : Game nO nL) (ρL : ℝ), 0 < ρL → ρL ≤ 1 →
    ∀ (j₀ : Fin nL), (∀ i, G.CL i j₀ = 0) → (∃ i, ∀ j, G.UL i j = 0 ∧ G.CL i j = 0) →
    ∀ T : ℕ, 1 ≤ T →
    (∀ (sel : Selector nL), IsValidSel j₀ ρL sel → ∀ (σ : Optimizer nO nL) {ω : Outcome nO nL},
        ω ∈ (law G σ ⟨T, ρL, j₀, sel⟩).support → ∀ t ∈ Finset.Icc 1 T,
          ω.total G.CL t ≤ t * ρL) ∧
    (∀ (sel : Selector nL), IsValidSel j₀ ρL sel → ∀ σ : Optimizer nO nL,
        expect (law G σ ⟨T, ρL, j₀, sel⟩) (fun ω => ω.total G.UO T) ≤
          G.BSE ρL * T + C * ((Real.sqrt nO * nL + Real.sqrt nL / ρL) * (Real.sqrt T + G.nHat))) ∧
    (∀ ρO : ℝ, 0 < ρO → ρO ≤ 1 → (∃ i, ∀ j, G.CO i j = 0) →
      ∀ (sel : Selector nL), IsValidSel j₀ ρL sel → ∀ σ : Optimizer nO nL,
        expect (law G σ ⟨T, ρL, j₀, sel⟩) (fun ω => ω.total G.CO T) ≤ ρO * T →
        expect (law G σ ⟨T, ρL, j₀, sel⟩) (fun ω => ω.total G.UO T) ≤
          G.BSE₂ ρL ρO * T +
            C / ρO * ((Real.sqrt nO * nL + Real.sqrt nL / ρL) * (Real.sqrt T + G.nHat))) ∧
    (∀ (sel : Selector nL), IsValidSel j₀ ρL sel → ∀ (σ : Optimizer nO nL) (S : ℕ), 1 ≤ S →
        ∀ (I : Fin S → Finset ℕ) (x : Fin S → Fin nO → ℝ), IsPiecewiseStationary σ T S I x →
        ∀ (s : Fin S), ∀ yS ∈ G.BRx ρL (x s),
          ((I s).card : ℝ) * (x s ⬝ᵥ (G.UL *ᵥ yS)) - C * (Real.sqrt (S * nL * T) / ρL) ≤
            expect (law G σ ⟨T, ρL, j₀, sel⟩) (fun ω => ∑ t ∈ I s, ω.entry G.UL t)) ∧
    (IsValidSel j₀ ρL (vertexSel j₀ ρL) ∧
      ∀ (σ : Optimizer nO nL) {ω : Outcome nO nL},
        ω ∈ (law G σ ⟨T, ρL, j₀, vertexSel j₀ ρL⟩).support → ∀ t ∈ Finset.Icc 1 T,
          ω.chargedAt t ≤ a * (T + nL) ^ d) := by sorry

end LearnVsOpt
