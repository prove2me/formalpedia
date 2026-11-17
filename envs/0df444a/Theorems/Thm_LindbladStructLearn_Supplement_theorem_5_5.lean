-- Prove2me | Theorems.Thm_LindbladStructLearn_Supplement_theorem_5_5
-- name    : LindbladStructLearn.Supplement.theorem_5_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:43:35.213202+00:00
-- url     : https://prove2.me/theorems/d238a28b-0780-404a-9074-aa45cd1ce9c1
-- title:
--   Theorem 5.5 — estimates $\widehat{\mathcal F}(x)$ at adaptive iterates to $\eta$ in $\infty$-norm with $O(C^k\log(n/\delta)/(t\eta^2))$ evolution time
-- statement:
--   Let $\mathcal L=\mathcal L_\lambda$ be a $k$-local Lindbladian on $n\ge1$ qubits with local one-norm $\|\mathcal L\|_{B_1}\le g$, $g>0$. Let $t,\eta>0$ with
--   $$t<\frac{1}{8ekg},\qquad t\eta\le1,$$
--   and let $\delta\in(0,1)$ and $T\ge0$. Write $\mathcal F(x)=\frac1t E(x)-\frac1t E(\lambda)$ for the error vector of Eq. (5.75). There is one algorithm, fixed in advance for each $k$, with the following properties. It first runs a preprocessing phase that uses the evolution $e^{\tau\mathcal L}$. It then answers $T$ queries. The $j$-th query point is $x^{(j)}$, any vector with $\|x^{(j)}\|_{B_1}\le 2g$ chosen as a function of the estimates already returned, as Algorithm 4's iterates are. For each query it returns an estimate $\widehat{\mathcal F}_j$. With probability at least $1-\delta$,
--   $$\|\mathcal F(x^{(j)})-\widehat{\mathcal F}_j\|_\infty\le\eta\qquad\text{for all }j<T.$$
--   Its total evolution time is at most $C_0C^k\log(2n/\delta)/(t\eta^2)$ for absolute constants $C_0,C>0$. Its total classical work is at most $C_k\,n^kT'\log(2nT'/\delta)/(t\eta)^2$ on every run, where $T'=\max(T,1)$ and $C_k$ depends only on $k$.
--
--   This is the resource analysis of Algorithm 4. Together with Theorem 5.2 it gives Theorem 5.1, and hence the evolution-time and runtime bounds of Theorem 1.1.
--
--   **Formalization Note** The algorithm is an admissible program of the published learner's machine run as an interactive session (`feedPoint`, `SessReach`, `sessionExp`). Its input is $n,T,g,t,\eta,\delta$; the unknown Lindbladian enters only through the experiments.
--
--   Differences from the source:
--   - generalization: iterates x in Algorithm 4, which satisfy ∥x∥_B1 ≤ 2g → query points chosen by an arbitrary rule next(F̂_0, …, F̂_(j−1)) of the revealed estimates with ∥x∥_B1 ≤ 2g at every point; reason: Algorithm 4's iterates are such a rule; the proof (footnote 8, p.41) only uses independence conditioned on the earlier rounds, which holds for every adaptive rule
--   - reading: with probability at least 1 − δ (δ not quantified in the statement) → for every δ ∈ (0,1), all T estimates simultaneously η-accurate with probability at least 1 − δ; reason: the proof takes δ as an input and union-bounds over the iterates and the terms (p.41)
--   - encoding: Let d = deg_{ε/(100·16^k)}(L) → omitted; reason: d and ε occur neither in the hypotheses nor in the conclusion
--   - encoding: there exists an algorithm for computing estimates F̂(x) → an admissible program of the published learner machine, chosen per k before n, g, t, η, δ, T, λ, run as an interactive session in which each query point is written into the halted learner's output block and the decoded next output is the estimate; reason: a resource statement needs a machine; the published machine is the one of Theorem 1.1, and the session is how the iterates reach the estimator
--   - encoding: t_total = O(C^k log(n/δ)/(tη²)) for some absolute constant C > 0 → the sum of the evolution durations on every complete session is at most C₀·C^k·log(2n/δ)/(tη²) with absolute C₀, C > 0; reason: O(·) as an explicit constant; log(2n/δ) replaces log(n/δ), which vanishes at n = 1, δ → 1
--   - encoding: classical runtime O((n^k T/(tη)²) log(nT/δ)), k = O(1) → every run of every phase halts within W steps and the total work of the session is at most W = ⌈C_k n^k T′/(tη)² log(2nT′/δ)⌉, T′ = max(T,1), C_k depending only on k; reason: O(·) with a k-dependent constant on every run; max(T,1) and the factor 2 keep the bound positive at T = 0 and n = 1
-- source:
--   Lewis–Tang–Wright, Learning the structure of open quantum systems, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), Theorem 5.5, p.40; proof pp.40–42

import Mathlib
import Definitions.Def_LindbladStructLearn_Supplement_Session
import Definitions.Def_LindbladStructLearn_Admissible
import Definitions.Def_LindbladStructLearn_Fvec
import Definitions.Def_LindbladStructLearn_IsLindbladParams
import Definitions.Def_LindbladStructLearn_IsKLocal
import Definitions.Def_LindbladStructLearn_b1Norm
import Definitions.Def_LindbladStructLearn_lindbladSuper

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal

namespace LindbladStructLearn.Supplement

open LindbladTolerant.Testing LindbladStructLearn

/-- Theorem 5.5 (Lewis–Tang–Wright, *Learning the structure of open quantum systems*,
arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), p.40). Let `L = L_λ` be a `k`-local
Lindbladian with `‖L‖_B1 ≤ g`, and let `t, η > 0` with `t < 1/(8ekg)` and `tη ≤ 1`. For iterates `x`
with `‖x‖_B1 ≤ 2g` there is an algorithm computing estimates `F̂(x)` of `F(x)` for all `T ≥ 0`
iterations such that `‖F(x) − F̂(x)‖_∞ ≤ η` with probability at least `1 − δ`, using total evolution
time `O(C^k log(n/δ)/(tη²))` for an absolute constant `C > 0`, and classical runtime
`O((n^k T/(tη)²) log(nT/δ))` (with `k = O(1)`).

**Formalization Note**
1. The algorithm is one admissible program of the published learner's machine, chosen after `k`
   (before `n, g, t, η, δ, T, λ`); its quantum access is the `experiment` instruction with
   `evo τ = e^(τ L)`. It runs as an interactive session: from the input `n, T` (integer cells 0, 1),
   `g, t, η, δ` (real cells 0–3) it runs until it halts (preprocessing), then `T` rounds; in round
   `j` the environment writes the query point `x^(j) = next(F̂_0, …, F̂_(j−1))` into the halted
   learner's output block (`feedPoint`), the learner resumes and halts again, and its decoded output
   is `F̂_j`. The machine state persists across rounds.
2. The query points are an arbitrary adaptive rule `next` of the revealed estimates with
   `‖x‖_B1 ≤ 2g` at every point: Algorithm 4's iterates are one such rule. The `T` estimates are
   simultaneously `η`-accurate with probability at least `1 − δ` (`δ ∈ (0,1)` is free).
3. Evolution time `≤ C₀ C^k log(2n/δ)/(tη²)` with `C₀, C` absolute; runtime: every run of every phase
   halts within `W` steps, and the total work of the whole session is at most
   `W = ⌈C_k n^k T'/(tη)² log(2nT'/δ)⌉` with `T' = max(T, 1)` and `C_k` depending only on `k`.
   Probabilities count only phases that halt within `W` steps (all do). -/
theorem theorem_5_5 :
    ∃ C₀ C : ℝ, 0 < C₀ ∧ 0 < C ∧ ∀ k : ℕ, 1 ≤ k → ∃ Ck : ℝ, 0 < Ck ∧ ∃ P : Program, Admissible P ∧
      ∀ n : ℕ, 1 ≤ n → ∀ g : ℝ, 0 < g → ∀ t η : ℝ, 0 < t → t < 1 / (8 * Real.exp 1 * k * g) →
      0 < η → t * η ≤ 1 → ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ T : ℕ,
      ∀ lam : Pauli n × Pauli n → ℂ, IsLindbladParams lam → IsKLocal k lam → b1Norm lam ≤ g →
      ∀ next : List (Idx n k → ℂ) → Idx n k → ℂ, (∀ h, b1Norm (ext (next h)) ≤ 2 * g) →
        let evo : ℝ → Super (Qubits n) (Qubits n) := fun τ => evolution (lindbladSuper lam) τ
        let s₀ : MState := listInput [(n : ℤ), (T : ℤ)] [g, t, η, δ]
        let T' : ℝ := max (T : ℝ) 1
        let W : ℕ := ⌈Ck * (n : ℝ) ^ k * T' / (t * η) ^ 2 * Real.log (2 * n * T' / δ)⌉₊
        (∀ s, Reach P n evo W s₀ s → Halted s) ∧
        (∀ s₁ (r : ℕ) h s, Reach P n evo W s₀ s₁ → SessReach P n k evo W next r [] s₁ h s →
          r < T → ∀ s', Reach P n evo W (feedPoint n k (next h) s) s' → Halted s') ∧
        (∀ s₁ h s, Reach P n evo W s₀ s₁ → SessReach P n k evo W next T [] s₁ h s →
          s.work ≤ W ∧ s.durations.sum ≤ C₀ * C ^ k * Real.log (2 * n / δ) / (t * η ^ 2)) ∧
        1 - ENNReal.ofReal δ ≤ wexp P n evo W s₀ (fun s₁ => by
          classical
          exact if Halted s₁ then
            sessionExp P n k evo W next (fun h _ =>
              if ∀ j < T, ‖Fvec t (toIdx lam) (next (h.take j)) - h.getD j 0‖ ≤ η then 1 else 0)
              T [] s₁
          else 0) := by sorry

end LindbladStructLearn.Supplement
