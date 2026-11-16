-- Prove2me | Theorems.Thm_GMRDiversity_Supplement_theorem_2
-- name    : GMRDiversity.Supplement.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:10:59.194948+00:00
-- url     : https://prove2.me/theorems/6908e580-14de-4baf-b63b-67ae5da61834
-- title:
--   Theorem 2 — all three operators are necessary
-- statement:
--   There is a universal constant $\gamma>0$ with the following property. For all $G,R,M\in\mathbb N_{>0}$ and $c_G,c_R,c_M\in\mathbb N_{>0}$ there is a GMR framework $\mathcal G=(X,U,\mathcal D,c,\mathrm{Obs})$ such that
--
--   1. $U:X\to[0,3]$;
--   2. feedback is full;
--   3. $\mathcal G$ has exactly one generation, one mutation and one recombination operator, of costs $c_G$, $c_M$ and $c_R$ respectively;
--
--   and, writing $B:=10Gc_G+Rc_R+Mc_M$, every policy $\pi$ and every $T\in\mathbb N$ with
--   $$
--   V^\pi_T(\mathcal G)\ \ge\ \tfrac{9}{10}\,V^*_B(\mathcal G)
--   $$
--   satisfy
--   $$
--   \Pr\big[G^\pi_T\ge\gamma G\ \text{ and }\ M^\pi_T\ge\gamma M\ \text{ and }\ R^\pi_T\ge\gamma R\big]\ \ge\ \tfrac12,
--   $$
--   where $G^\pi_T,M^\pi_T,R^\pi_T$ count the generation, mutation and recombination queries among the first $T$ rounds.
--
--   The policy $\pi$ is any adaptive randomized policy of $\mathcal G$, with no budget; only the benchmark $V^*_B$ is budget-constrained. So any policy reaching $9/10$ of the optimal budget-$B$ value must, with constant probability, use $\Omega(G)$ generations, $\Omega(M)$ mutations and $\Omega(R)$ recombinations.
--
--   **Formalization Note** $\gamma$ is chosen before $G,R,M,c_G,c_R,c_M$; the framework, a `GMRFramework` on a measurable space `X : Type`, may depend on all six. The three counts are compared with $\gamma G,\gamma M,\gamma R$ as real numbers inside one event. $V^\pi_T$ and $V^*_B$ are extended reals.
--
--   Differences from the source:
--   - generalization: there is a GMR framework (Definition 1: recombination rules of any arity k ≥ 2) with U : X → [0, 3], full feedback and one generation, recombination and mutation operator → there is a GMRFramework on a measurable space X : Type with measurable U, a probability measure, a 1-input and a 2-input Markov kernel, ∀ x, 0 ≤ U x ≤ 3; reason: the Lean existential ranges over a narrower class of frameworks (recombination exactly 2-input, measurable data), so it implies the source's claim; the paper's witness on [0,1]² with deterministic measurable mutation and 2-input midpoint recombination is in this class, and measurability makes the expectations well-defined as p.3 assumes
--   - encoding: V^π_T ≥ (9/10)V*_B → ((9/10 : ℝ) : EReal) * Vstar F B ≤ value π T, policies as Markov kernels of the history; reason: the extended-real value and policy class of the definitions items, which agree with the paper's whenever its expectations are defined
--   - reading: simultaneously apply at least γG generations, γM mutations and γR recombinations → the counts among the first T rounds, one event of probability ≥ 1/2; reason: the proof (p.17) concludes "simultaneously applies … within its first T rounds"
-- source:
--   A. Brandenberger, I. Doron-Arad, E. Mossel, Genetic Algorithms with Optimization Guided Operators, STOC 2027 submission (manuscript sha256 f89f4f770d5d05df82f0407a81287ce4ccf618727beb5415eef3ad56c36b6cbe), Theorem 2, p.7 (restated p.15; proof pp.15–17)

import Mathlib
import Definitions.Def_GMRDiversity_Supplement_value

namespace GMRDiversity.Supplement

open MeasureTheory ProbabilityTheory

/-- **Theorem 2 (All three operators are necessary)** (Brandenberger, Doron-Arad, Mossel, *Genetic
Algorithms with Optimization Guided Operators*, STOC 2027 submission, manuscript sha256 f89f4f77…,
Theorem 2, p.7; restated p.15, proof pp.15–17): there is a universal constant `γ > 0` such that for
all `G, R, M ∈ ℕ_{>0}` and `c_G, c_R, c_M ∈ ℕ_{>0}` there is a GMR framework with `U : X → [0, 3]`,
full feedback, and one generation, recombination and mutation operator of costs `c_G, c_R, c_M`,
such that, for `B := 10 G c_G + R c_R + M c_M`, any policy `π` and `T ∈ ℕ` with
`V^π_T ≥ (9/10) V*_B` must, with probability at least `1/2`, simultaneously apply at least `γG`
generations, `γM` mutations and `γR` recombinations (among its first `T` rounds).

**Formalization Note.** `γ` is chosen before `G, R, M, c_G, c_R, c_M`; the framework (a
`GMRFramework` on some measurable space `X : Type`) depends on all six. The policy `π` ranges over
all adaptive randomized policies of that framework, with no cost bound; only `V*_B` is
budget-constrained. The three counts are compared with `γG, γM, γR` as real numbers inside one
event. -/
theorem theorem_2 : ∃ γ : ℝ, 0 < γ ∧ ∀ G R M cG cR cM : ℕ, 0 < G → 0 < R → 0 < M → 0 < cG →
    0 < cR → 0 < cM →
    ∃ (X : Type) (_ : MeasurableSpace X) (F : GMRFramework X),
      (∀ x, 0 ≤ F.U x ∧ F.U x ≤ 3) ∧ F.cG = cG ∧ F.cM = cM ∧ F.cR = cR ∧
      ∀ (π : Policy F) (T : ℕ),
        ((9 / 10 : ℝ) : EReal) * Vstar F (10 * G * cG + R * cR + M * cM) ≤ value π T →
        (1 / 2 : ENNReal) ≤ runLaw π {ω | γ * G ≤ (numGen T ω : ℝ) ∧ γ * M ≤ (numMut T ω : ℝ) ∧
          γ * R ≤ (numRec T ω : ℝ)} := by sorry

end GMRDiversity.Supplement
