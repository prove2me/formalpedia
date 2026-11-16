-- Prove2me | Theorems.Thm_GMRDiversity_Supplement_theorem_4
-- name    : GMRDiversity.Supplement.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:11:33.092202+00:00
-- url     : https://prove2.me/theorems/a41a15b2-d42f-4952-a238-f3dbf1a4db76
-- title:
--   Theorem 4 — memory is necessary for parity learning
-- statement:
--   Consider parity learning $\mathfrak G^{\mathrm{par}}_x$ with $x\sim\mathrm{Unif}(\{0,1\}^n)$ drawn independently of the policy, full feedback, and policies whose entire persistent state after each round is $S_t\in\{0,1\}^M$ ("$M$ bits of memory"). There exist constants $c,C,\alpha>0$, and a constant $K>0$ for the $O(\cdot)$, such that for every $n\ge2$:
--
--   1. there is a policy $\pi$ using at most $Cn^2$ bits of memory, whose recombinations only combine previously queried candidates, and a horizon $T\le Cn$ such that
--   $$
--   V^\pi_T(\mathfrak G^{\mathrm{par}}_x)\ \ge\ \tfrac23;
--   $$
--   2. every policy $\pi$ using at most $cn^2$ bits of memory satisfies, for every $T\le2^{\alpha n}$,
--   $$
--   V^\pi_T(\mathfrak G^{\mathrm{par}}_x)\ \le\ K\,2^{-\alpha n}.
--   $$
--
--   So $\Theta(n^2)$ bits of memory are exactly what parity learning needs: with $O(n^2)$ bits a linear number of queries suffices, while with $cn^2$ bits even exponentially many queries succeed only with exponentially small probability.
--
--   **Formalization Note** "Using at most $cn^2$ bits" is $M\le cn^2$ for a state in `Fin M → Bool`. $V^\pi_T$ is the probability that some $z_t$, $t\le T$, has first coordinate $x$, averaged over $x$. Part 2 is stated for every memory-$M$ policy, including those whose XOR arguments are arbitrary values computed from the state.
--
--   Differences from the source:
--   - generalization: every policy π using at most cn² bits of memory, whose operator inputs are recoverable from S_t (previously queried candidates) → every MemoryPolicy n M with M ≤ cn², whose XOR arguments may be any values drawn from a law depending on S_{t−1}; reason: the paper's policies are the subclass satisfying XorOfQueried, so part (ii) for all MemoryPolicy specializes to the source's part (ii)
--   - reading: V^π_T ≤ O(2^{−αn}) → V^π_T ≤ K·2^{−αn} with one K > 0 chosen together with c, C, α before n; reason: the uniform reading of O in a statement quantified over n; the proof's constant is that of Raz's O(2^{−βn})
--   - encoding: memory M up to time T → state Fin M → Bool, initial state, kernels act(t, S_{t−1}) and upd(t, S_{t−1}, action, z_t, U_x(z_t)), the bound imposed at every round; reason: the page's model; fresh randomness and the round index are free, and rounds after T do not affect V^π_T
--   - encoding: V^π_T(𝔊^par_x) = E[max_{t ≤ T} U_x(z_t)] averaged over x → (1/2ⁿ) Σ_x P(some z_t, t ≤ T, has first coordinate x); reason: U_x ∈ {0,1}, so the expected maximum is the hit probability
--   - encoding: a policy using at most Cn² bits and T ≤ Cn queries → ∃ M with M ≤ Cn², a MemoryPolicy n M with XorOfQueried and ∃ T with T ≤ Cn; reason: the page's policy recombines retained (queried) equations, the strict reading of p.4 and p.9
-- source:
--   A. Brandenberger, I. Doron-Arad, E. Mossel, Genetic Algorithms with Optimization Guided Operators, STOC 2027 submission (manuscript sha256 f89f4f770d5d05df82f0407a81287ce4ccf618727beb5415eef3ad56c36b6cbe), Theorem 4, p.9 (restated p.12; proof §6.2, pp.12–13)

import Mathlib
import Definitions.Def_GMRDiversity_Supplement_MemoryPolicy

namespace GMRDiversity.Supplement

open ExtremalForrelation.Nonadaptive

/-- **Theorem 4 (Memory is necessary)** (Brandenberger, Doron-Arad, Mossel, *Genetic Algorithms
with Optimization Guided Operators*, STOC 2027 submission, manuscript sha256 f89f4f77…, Theorem 4,
p.9; restated p.12, proof pp.12–13): there exist `c, C, α > 0` such that for every `n ≥ 2`:
(i) there is a policy `π` using at most `Cn²` bits of memory and `T ≤ Cn` queries such that
`V^π_T(𝔊^par_x) ≥ 2/3`;
(ii) every policy `π` using at most `cn²` bits of memory satisfies, for every `T ≤ 2^{αn}`,
`V^π_T(𝔊^par_x) ≤ O(2^{−αn})`.

**Formalization Note.** The constant `K` hidden in `O(2^{−αn})` is chosen together with
`c, C, α`, before `n`. Part (i) produces a policy whose XOR arguments are previously queried
candidates (`XorOfQueried`); part (ii) covers every memory-`M` policy, whose XOR arguments may be any
values computed from the state (a broader class). "At most `cn²` bits" is `M ≤ c n²` for the
number `M` of bits of the state `Fin M → Bool`. -/
theorem theorem_4 : ∃ c C α K : ℝ, 0 < c ∧ 0 < C ∧ 0 < α ∧ 0 < K ∧ ∀ n : ℕ, 2 ≤ n →
    (∃ M : ℕ, (M : ℝ) ≤ C * (n : ℝ) ^ 2 ∧ ∃ π : MemoryPolicy n M, π.XorOfQueried ∧
      ∃ T : ℕ, (T : ℝ) ≤ C * n ∧ 2 / 3 ≤ memValue π T) ∧
    (∀ M : ℕ, (M : ℝ) ≤ c * (n : ℝ) ^ 2 → ∀ (π : MemoryPolicy n M) (T : ℕ),
      (T : ℝ) ≤ (2 : ℝ) ^ (α * n) → memValue π T ≤ K * (2 : ℝ) ^ (-(α * n))) := by sorry

end GMRDiversity.Supplement
