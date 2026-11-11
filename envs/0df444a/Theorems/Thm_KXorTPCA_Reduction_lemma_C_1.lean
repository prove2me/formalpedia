-- Prove2me | Theorems.Thm_KXorTPCA_Reduction_lemma_C_1
-- name    : KXorTPCA.Reduction.lemma_C_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:24:32.376239+00:00
-- url     : https://prove2.me/theorems/83c8ebb4-b122-46f5-a4f8-43d7f6234e09
-- title:
--   Lemma C.1 — a detection reduction transfers a detection algorithm back, with Type I+II error at most 2ρ_n + δ_{n^c}
-- statement:
--   Let $P=(P_n)$ and $Q=(Q_n)$ be sequences of planted problems (given by measurable samplers), $c>0$, and $d:\mathbb N\to\mathbb N$ with $d(n)\le n^c$. Let $R$ be a program running in time $C_R n^r+C_R$ that, for every $n$, is an average-case reduction for detection (Definition C.4) from $P_n$ to $Q_{d(n)}$ with TV-error $\rho_n$. Let $B$ be a program running in time $C_B n^t+C_B$ whose Type I + II error on $Q_n$ is at most $\delta_n$ for every $n$. Then there are a program $A$ and a constant $C$ such that $A$ runs in time $C(n^{ct}+n^r)+C$ and, for every $n$,
--
--   $$\mathrm{err}_n(A;P_n)\ \le\ 2\rho_n+\delta_{d(n)} .$$
--
--   This is the basic algorithm-transfer property of an average-case reduction for detection.
--
--   Differences from the source:
--   - generalization: $n'=n^c$ → any dimension map with $d(n)\le n^c$; reason: the proof uses only the running time of $B$ at dimension $d(n)\le n^c$; $d(n)=\lfloor n^c\rfloor$ is the source's case.
--   - generalization: Definition C.4's "there exists some $x'$" → a possibly random $x'$ drawn by the reduction; reason: a weaker hypothesis on $R$; the deterministic $x'$ of the source is the special case.
--   - reading: $O(n^r)$, $O(n^t)$, $O(n^{ct}+n^r)$-time → explicit worst-case bounds $C_Rn^r+C_R$, $C_Bn^t+C_B$, $C(n^{ct}+n^r)+C$ (real exponents $r,t$) on every input whose cell $0$ is $n$ and every tape; reason: the machine model of the mission.
--   - encoding: algorithms and reductions → programs of the randomized real RAM, the reduction's output being its final memory; reason: the paper fixes no machine.
--   - encoding: the problems $P$, $Q$ → samplers from random tapes, assumed measurable; reason: a distribution is the law of a measurable sampler (a non-measurable sampler has no law, and its push-forward would be the zero measure).
-- source:
--   G. Bresler, A. Harbuzova, Average-Case Reductions for k-XOR and Tensor PCA, arXiv:2601.19016 (copy sha256 6ec029a7…), p. 97 (PDF 100), Lemma C.1

import Mathlib
import Definitions.Def_KXorTPCA_Reduction_Reductions

namespace KXorTPCA.Reduction

theorem lemma_C_1 (P Q : (n : ℕ) → Task n) (d : ℕ → ℕ) (c : ℝ) (hc : 0 < c)
    (hd : ∀ n, (d n : ℝ) ≤ (n : ℝ) ^ c)
    (hPm : ∀ n, Measurable (P n).null ∧ ∀ x, Measurable ((P n).planted x))
    (hQm : ∀ n, Measurable (Q n).null ∧ ∀ x, Measurable ((Q n).planted x))
    (R : Program) (r : ℝ) (Cr : ℕ)
    (hR : ∀ (n : ℕ) (y : ℤ → ℝ), y 0 = n → ∀ ω : Tapes,
      HaltsWithin R y ω ((Cr : ℝ) * (n : ℝ) ^ r + Cr))
    (ρs : ℕ → ℝ) (hred : ∀ n, IsDetReduction R (P n) (Q (d n)) (ρs n))
    (B : Program) (t : ℝ) (Cb : ℕ)
    (hB : ∀ (n : ℕ) (y : ℤ → ℝ), y 0 = n → ∀ ω : Tapes,
      HaltsWithin B y ω ((Cb : ℝ) * (n : ℝ) ^ t + Cb))
    (δs : ℕ → ℝ) (hδ : ∀ n, detErr B (Q n) ≤ δs n) :
    ∃ (A : Program) (C : ℝ),
      (∀ (n : ℕ) (y : ℤ → ℝ), y 0 = n → ∀ ω : Tapes,
        HaltsWithin A y ω (C * ((n : ℝ) ^ (c * t) + (n : ℝ) ^ r) + C)) ∧
      ∀ n, detErr A (P n) ≤ 2 * ρs n + δs (d n) := by sorry

end KXorTPCA.Reduction
