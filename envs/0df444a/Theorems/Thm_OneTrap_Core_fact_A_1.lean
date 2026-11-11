-- Prove2me | Theorems.Thm_OneTrap_Core_fact_A_1
-- name    : OneTrap.Core.fact_A_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:45:46.640483+00:00
-- url     : https://prove2.me/theorems/a271e918-d109-4f28-8b2f-24029534ab9a
-- title:
--   Fact A.1 — both lexicographic maxima are attained, $V_P(w\mid A)>-\infty$ iff every wage is integrable, and then a deterministic measurable lexicographic maximizer exists
-- statement:
--   For every finite technology $A$ and every contract $w\in W$ (not only $W_{\mathrm{eff}}$): the primary optimum $\max_\pi U_A(w,\pi)$ and the principal-favored secondary maximum are attained; moreover
--   $$V_P(w\mid A)>-\infty\iff \mathbb E[w(Y_i)]<\infty\ \text{for every } i\in A;$$
--   on the finite branch $V_P(w\mid A)\in\mathbb R$ and a deterministic measurable lexicographic maximizer exists; otherwise $V_P(w\mid A)=-\infty$.
--
--   Differences from the source:
--   - encoding: box i: output law F_i on [0, ∞), integrable (Assumption 2.1), deterministic cost c_i ≥ 0 → `Box`: a `ProbabilityMeasure ℝ` with nonnegative outputs almost surely and integrable identity, and a real cost ≥ 0; a technology is `T : ι → Box` with `[Fintype ι]`, joint law the product measure; reason: the same objects; independence is the product law
--   - encoding: a contract is a Borel function w : R+ → R+; W_eff adds w(0) = 0 and w(y) ≤ L(1 + y) for one L < ∞ → `w : ℝ → ℝ` Borel on ℝ with `0 ≤ w y` for `y ≥ 0` (`IsContract`), plus `w 0 = 0` and `∃ L, ∀ y ≥ 0, w y ≤ L * (1 + y)` (`IsEffContract`); reason: outputs are almost surely nonnegative, so values of w on (−∞, 0) never matter, and every Borel function on R+ extends to a Borel function on ℝ
--   - encoding: a policy assigns to every history (distinct actions with observed outputs) a probability distribution over taking an unopened action or stopping and submitting the null output or an observed output, Borel in the observed outputs → `Policy`: a rule of the opened set S, the outputs y (pre-sampled from the product law) and one seed u uniform on [0, 1] that reads y only on S, is measurable, opens only unopened boxes and submits only available outcomes; reason: the order in which S was opened is itself a function of the rule, y on S and u, and one uniform seed generates independent randomizations for every step (and conversely), so the laws of (opened set, submitted output) are the same
--   - encoding: expected payoffs U_A, P_A in the extended reals (Appendix A) → `eexp`: lower Lebesgue integral of the positive part minus that of the negative part, in EReal; reason: the convention of Appendix A; never the Bochner integral; ⊤ − ⊤ (= ⊥ in EReal) does not arise for these payoffs because the agent payoff is bounded below and the principal payoff above by integrable variables
--   - encoding: V_P(w | A) = max of P_A(w, π) over Σ⋆(w, A) = argmax U_A(w, ·) (Definition 2.2) → `VP w T` = `sSup` in EReal of `principalValue` over `agentOptimal` (⊥ if that set were empty); the null output is the initial outcome with pair (w 0, 0 − w 0); reason: both maxima are attained (Fact A.1), and an attained supremum is the maximum
--   - encoding: the primary optimum and the PF secondary maximum are attained; a deterministic measurable lexicographic maximizer → `agentOptimal` is nonempty and contains a π with `principalValue π = VP w T`; on the finite branch such a π with `π.IsDeterministic` (rule independent of the seed); measurability is part of `Policy`; reason: the same claims
--   - encoding: E[w(Y_i)] < ∞; V_P(w | A) ∈ ℝ → `∫⁻ y, ENNReal.ofReal (w y) ∂F_i < ⊤`; `VP w T ≠ ⊥ ∧ VP w T ≠ ⊤`; reason: w ≥ 0 on the support, so the lower integral is E[w(Y_i)]
-- source:
--   Feldman, Fu, Peng, Tang (2026), One Trap Is Enough: The Structure and Complexity of Robust Contracts for Sequential Search, held STOC 2027 submission (SHA-256 8b684ffb…cf066), Fact A.1, p. 19 (PDF 20)

import Mathlib
import Definitions.Def_OneTrap_Core_Model
import Definitions.Def_OneTrap_Core_Search

open MeasureTheory

namespace OneTrap.Core

/-- Fact A.1 (p. 19). For every finite technology `A` and every contract `w ∈ W`: the primary
optimum and the principal-favored secondary maximum are attained; `V_P(w | A) > −∞` iff
`E[w(Y_i)] < ∞` for every box; on that branch `V_P(w | A)` is real and a deterministic
measurable lexicographic maximizer exists; otherwise `V_P(w | A) = −∞`. -/
theorem fact_A_1 {ι : Type*} [Fintype ι] [DecidableEq ι] (w : ℝ → ℝ) (hw : IsContract w)
    (T : ι → Box) :
    (agentOptimal w T Finset.univ (nullPair w)).Nonempty ∧
    (∃ π ∈ agentOptimal w T Finset.univ (nullPair w),
      principalValue w T (nullPair w) π = VP w T) ∧
    (⊥ < VP w T ↔ ∀ i, ∫⁻ y, ENNReal.ofReal (w y) ∂((T i).out.law : Measure ℝ) < ⊤) ∧
    ((∀ i, ∫⁻ y, ENNReal.ofReal (w y) ∂((T i).out.law : Measure ℝ) < ⊤) →
      VP w T ≠ ⊥ ∧ VP w T ≠ ⊤ ∧
      ∃ π ∈ agentOptimal w T Finset.univ (nullPair w),
        π.IsDeterministic ∧ principalValue w T (nullPair w) π = VP w T) ∧
    ((¬ ∀ i, ∫⁻ y, ENNReal.ofReal (w y) ∂((T i).out.law : Measure ℝ) < ⊤) →
      VP w T = ⊥) := by sorry

end OneTrap.Core
