-- Prove2me | Theorems.Thm_LindbladStructLearn_theorem_1_1
-- name    : LindbladStructLearn.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:05:24.033829+00:00
-- url     : https://prove2.me/theorems/acb611b7-80b2-47da-ba43-93c147bcf788
-- title:
--   Theorem 1.1 — learning a $k$-local Lindbladian to $\varepsilon$ in $B_1$ norm from Pauli experiments: evolution time $O(gd^2\log n/\varepsilon^2)$, runtime $\widetilde O(n^kg^2d^2/\varepsilon^2)$
-- statement:
--   Fix the locality $k \ge 1$. There are constants $C, c > 0$ depending only on $k$ and one admissible program $\mathcal A$ on the learner's machine (classical real-RAM computation, fair coins, and experiments that prepare a Pauli eigenstate, apply $e^{\mathcal Lt}$ for a chosen $t$, and measure in a Pauli eigenbasis) such that the following holds. For every $n \ge 1$, $g > 0$, $d \in \mathbb N$, $\varepsilon > 0$, $\delta \in (0,1)$, and every $k$-local Lindbladian $\mathcal L = \mathcal L_\lambda$ on $n$ qubits ($\alpha$ purely imaginary, $D \succeq 0$) with
--
--   $$\|\mathcal L\|_{B_1} \le g \qquad\text{and}\qquad \deg_{\varepsilon/(100\cdot16^k)}(\mathcal L) \le d,$$
--
--   the program, given $(n, d, g, \varepsilon, \delta)$ and access to $\mathcal L$ only through its experiments, outputs estimates $\widehat\lambda = (\widehat\alpha, \widehat D)$ such that:
--
--   1. **(Accuracy)** with probability at least $1-\delta$, $\|\widehat{\mathcal L} - \mathcal L\|_{B_1} \le \varepsilon$, and every coefficient is within $\varepsilon$, so $\|\widehat\alpha - \alpha\|_\infty \le \varepsilon$ and $\|\widehat D - D\|_\infty \le \varepsilon$;
--   2. **(Evolution time)** on every run the total evolution time is at most $C\,g\,d^2\log(2n/\delta)/\varepsilon^2$;
--   3. **(Time resolution)** every applied evolution time is at least $c/g$;
--   4. **(Quantum measurements)** on every run it performs at most $C\,g^2d^2\log(2n/\delta)/\varepsilon^2$ experiments;
--   5. **(Classical overhead)** every run halts within $\lceil C R\rceil$ steps, where
--
--   $$R = 1 + n^k\Big(\frac{gd}{\varepsilon}\Big)^2\,\ell\,\log\frac{2n\ell}{\delta}, \qquad \ell = 1 + \max\{0, \log(g/\varepsilon)\}.$$
--
--   With $\delta = 0.01$ this is Theorem 1.1: the structure and coefficients of an unknown local Lindbladian are learned from simple Pauli experiments with a total evolution time that scales logarithmically in the number of qubits.
--
--   Differences from the source:
--   - generalization: probability 0.99 → probability at least 1 − δ for every δ ∈ (0,1), with log(2n/δ) in items 2 and 4 (Theorem 5.1's δ); reason: δ = 1/100 gives item 1, and log(200n) ≤ 9 log n for n ≥ 2
--   - reading: log(n) in items 2 and 4 → log(2n/δ); reason: at n = 1 the printed log n = 0 would allow no experiment, but the single-qubit dissipators λ_{Z,Z} = γ and 2γ cannot both be learned to ε < γ/2 without one; log(2n/δ) ≤ 2 log(n/δ) whenever n/δ ≥ 2
--   - reading: classical runtime O((n^k g² d²/ε²) log(g/ε) log(n log(g/ε))) → every run halts within ⌈C·(1 + n^k (gd/ε)² ℓ log(2nℓ/δ))⌉ steps, ℓ = 1 + max(0, log(g/ε)); reason: the printed expression is ≤ 0 when ε ≥ g or d = 0, where the zero output suffices (p.32); for ε < g, d ≥ 1 the two agree up to the constant; δ enters as in Theorem 5.1
--   - reading: classical runtime (unqualified) → a bound on every run (worst case); reason: the stronger reading; the paper's proof bounds it with probability 1 − δ/3, and aborting at a step budget (counted as failure) makes it worst case
--   - reading: t ≥ t_min = Θ(1/g) → ∃ c > 0 depending on k with every applied duration ≥ c/g; reason: the upper half of Θ only weakens "t ≥ t_min"
--   - reading: a quantum algorithm A with k = O(1); experiments of the form prepare a Pauli eigenstate, apply e^{Lt}, measure in a Pauli eigenbasis → one admissible program, chosen after k and before n, g, d, ε, δ and L, on a real RAM with integer pointers, fair coins and an experiment instruction (the only access to L); constants C, c depend only on k; reason: the paper fixes no machine; item 4 and Figure 1 fix the form of the quantum access
--   - encoding: deg_{ε/(100·16^k)}(L) ≤ d → ∃ μ with ‖λ − μ‖_B1 < ε/(100·16^k) and deg(μ) ≤ d; reason: the minimum in (2.9) is over a nonempty set of naturals
--   - encoding: L with coefficients α, D; estimates (α̂, D̂) → coefficient vectors on all pairs of Paulis with λ(I,·) = 0; the decoded output; reason: λ_{P,I} = α_P, λ_{P1,P2} = D_{P1,P2} (Eq. (2.5)); the map λ ↦ L_λ is injective on such vectors
--   - encoding: n qubits → n ≥ 1; reason: excludes only the degenerate system with no qubit, where log(n) is undefined
-- source:
--   Lewis–Tang–Wright, Learning the structure of open quantum systems, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), Theorem 1.1, p.4; Theorem 5.1 (failure probability δ), p.34

import Mathlib
import Definitions.Def_LindbladTolerant_Testing_lindblad_model
import Definitions.Def_LindbladStructLearn_Admissible
import Definitions.Def_LindbladStructLearn_Reach
import Definitions.Def_LindbladStructLearn_mass
import Definitions.Def_LindbladStructLearn_Halted
import Definitions.Def_LindbladStructLearn_decodeLindblad
import Definitions.Def_LindbladStructLearn_goalInput
import Definitions.Def_LindbladStructLearn_IsLindbladParams
import Definitions.Def_LindbladStructLearn_IsKLocal
import Definitions.Def_LindbladStructLearn_b1Norm
import Definitions.Def_LindbladStructLearn_ApproxDegLe
import Definitions.Def_LindbladStructLearn_lindbladSuper

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal

namespace LindbladStructLearn

open LindbladTolerant.Testing

/-- Theorem 1.1 (learning local Lindbladians from real-time evolution; Lewis–Tang–Wright, *Learning the structure of open quantum systems*, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), p.4, with the
failure probability `δ` of Theorem 5.1, p.34). Let `ε > 0` and `k = O(1)`. Let `L` be a `k`-local
Lindbladian with `‖L‖_B1 ≤ g` and `deg_(ε/(100·16^k))(L) ≤ d`. There is a quantum algorithm that
outputs `(α̂, D̂)` such that: (1) with probability `1 − δ`, `‖L̂ − L‖_B1 ≤ ε` (hence
`‖α̂ − α‖_∞, ‖D̂ − D‖_∞ ≤ ε`); (2) its total evolution time is `O(g d² log(n)/ε²)`; (3) it only
applies `e^(Lt)` with `t ≥ t_min = Θ(1/g)`; (4) it performs `O(g² d² log(n)/ε²)` experiments
(prepare a Pauli eigenstate, apply `e^(Lt)`, measure in a Pauli eigenbasis); (5) its classical
runtime is `O((n^k g² d²/ε²) log(g/ε) log(n log(g/ε)))`.

**Formalization Note**
1. The algorithm is one admissible program of the learner's machine (`Instr`, `branches`), chosen
   after `k` and before `n`, `g`, `d`, `ε`, `δ` and `L`; its only access to `L` is the
   `experiment` instruction with `evo t = e^(tL)`. Input: `n, d, g, ε, δ` (`goalInput`); output:
   the decoded vector `decodeLindblad` (coefficients on all pairs, `0` for `P₁ = I`).
2. Constants `C, c` depend only on `k` (`k = O(1)`). `δ ∈ (0,1)` is free (`δ = 0.01` is Theorem 1.1),
   and `log(2n/δ)` replaces `log n`, which is `0` at `n = 1`.
3. Item 5 holds on every run: after `N = ⌈C·R⌉` steps every run has halted with work `≤ N`, where
   `R = 1 + n^k (gd/ε)² ℓ log(2nℓ/δ)` and `ℓ = 1 + log⁺(g/ε)`. Items 2–4 hold on every reachable
   configuration (`durations` lists the evolution times applied); item 3 reads `t_min = Θ(1/g)` as
   "every duration is at least `c/g`".
4. `L` is given by a coefficient vector `λ` with `IsLindbladParams` (`α` imaginary, `D ⪰ 0`),
   `k`-local; the approximate degree bound is the `∃` form `ApproxDegLe`. -/
theorem theorem_1_1 (k : ℕ) (hk : 1 ≤ k) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∃ P : Program, Admissible P ∧
      ∀ n : ℕ, 1 ≤ n → ∀ g : ℝ, 0 < g → ∀ d : ℕ, ∀ ε : ℝ, 0 < ε → ∀ δ : ℝ, 0 < δ → δ < 1 →
      ∀ lam : Pauli n × Pauli n → ℂ, IsLindbladParams lam → IsKLocal k lam → b1Norm lam ≤ g →
        ApproxDegLe (ε / (100 * 16 ^ k)) lam d →
        let evo : ℝ → Super (Qubits n) (Qubits n) := fun τ => evolution (lindbladSuper lam) τ
        let ℓ : ℝ := 1 + max 0 (Real.log (g / ε))
        let R : ℝ := 1 + (n : ℝ) ^ k * (g * d / ε) ^ 2 * ℓ * Real.log (2 * n * ℓ / δ)
        let N : ℕ := ⌈C * R⌉₊
        (∀ s, Reach P n evo N (goalInput n d g ε δ) s → Halted s ∧ s.work ≤ N) ∧
        1 - ENNReal.ofReal δ ≤ mass P n evo N (goalInput n d g ε δ) (fun s => Halted s ∧
          b1Norm (decodeLindblad n k s - lam) ≤ ε ∧
          ∀ Q : Pauli n × Pauli n, ‖decodeLindblad n k s Q - lam Q‖ ≤ ε) ∧
        ∀ (M : ℕ) (s : MState), Reach P n evo M (goalInput n d g ε δ) s →
          s.durations.sum ≤ C * g * d ^ 2 * Real.log (2 * n / δ) / ε ^ 2 ∧
          (s.durations.length : ℝ) ≤ C * g ^ 2 * d ^ 2 * Real.log (2 * n / δ) / ε ^ 2 ∧
          ∀ τ ∈ s.durations, c / g ≤ τ := by sorry

end LindbladStructLearn
