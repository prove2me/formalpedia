-- Prove2me | Theorems.Thm_MCPoise_lemma_2_3
-- name    : MCPoise.lemma_2_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:36:56.507694+00:00
-- url     : https://prove2.me/theorems/8d46d69c-cd8d-45eb-93ab-296b76866ebf
-- title:
--   Lemma 2.3 — unit flows to the group root on paths of length at most $\rho^2 L_d = O(\log^3 k) L$
-- statement:
--   Let $(x, f, \lambda)$ be feasible for Junction-LP, and let $\rho$ be an integer with $\rho \ge 128 \log_2(2k)$.
--
--   **Lemma 2.3.** For every run of Algorithm 1, every returned group $C$ with representative $z^*_C$, and every terminal $t \in \bigcup_{z_i \in Z_C} \{s_i, t_i\}$, the construction of p.12 gives a unit flow from $t$ to $s^*_C$ on simple paths of length at most
--   $$L'_d = \rho^2 L_d.$$
--   For $\rho = \lceil 128 \log_2(2k) \rceil$, one has $L'_d = O(\log^3 k) L$.
--
--   Differences from the source:
--   - generalization: the algorithm's run with one implementation → every run of Algorithm 1 with every choice of representatives and shortest paths; reason: the page leaves those choices open, so one implementation is a special case
--   - reading: ρ ≥ 128 log(2k), base not printed → 128 log₂(2k) ≤ ρ; reason: Lemma 2.5's last line needs base 2: 64 log₂ k/(128 ln k) > 1/2
--   - encoding: terminal t ∈ ∪{s_i, t_i} → the label (i, b) of the demand occurrence; reason: footnote 2, p.9: a vertex in several demands has separate flow variables
--   - reading: t in the union includes s*_C with no flow described → the unit on the length-zero path; reason: the page is silent and this is the only flow from a vertex to itself
--   - reading: the printed $O(\cdot)$ in $\log k$ → the factor $\log(k+1)$ with one absolute constant; reason: $\log k$ vanishes at $k = 1$, and for $k \ge 2$ the two differ by a constant factor
-- source:
--   R. Jain, A. Niaparast, R. Ravi, Polylog Pairwise Poise: Approximating Multicommodity Multicast, STOC 2027 submission (manuscript sha256 2c6a7cc5…), Lemma 2.3, p.13

import Mathlib
import Definitions.Def_MCPoise_JunctionLPFeasible
import Definitions.Def_MCPoise_auxGraph
import Definitions.Def_MCPoise_AssignRun
import Definitions.Def_MCPoise_IsGroupFlow

namespace MCPoise

/-- **Lemma 2.3 (unit flows to the group's root).**
Jain, Niaparast, Ravi, *Polylog Pairwise Poise: Approximating Multicommodity Multicast*, STOC 2027 submission (manuscript sha256 2c6a7cc5…), Lemma 2.3, p.13: "For each group C and each terminal t ∈ ∪_{z_i∈Z_C}{s_i, t_i}, the algorithm described above yields unit flow
from t to s*_C supported on paths of length at most L′_d = ρ²L_d = O(log³ k)L."

First clause: for every run of Algorithm 1 from the auxiliary graph of a feasible solution, every group and every terminal `(i, b)` of the
group have a flow of the construction of p.12 made of simple paths from the terminal to `s*_C`, with nonnegative weights summing to
`1`, each path of length at most `ρ² L_d`. Second clause: `O(log³ k)L` for the smallest allowed integer `ρ = ⌈128 log₂(2k)⌉`, with one absolute
constant.

**Formalization Note.** `ρ` is an integer with `128 log₂(2k) ≤ ρ`, in base `2`: the proof of Lemma 2.5 needs that base. The factor `log(k + 1)` replaces
`log k`, which vanishes at `k = 1`. -/
theorem lemma_2_3 :
    (∀ (I : Inst) (L : ℕ) (x : Sym2 (Fin I.n) → ℝ) (x' : Sym2 (Fin I.n) → Fin I.k → ℝ)
      (lam : Fin I.k → Fin I.k → ℝ) (f : Fin I.k → Bool → Fin I.k → List (Fin I.n) → ℝ) (ρ : ℕ),
      JunctionLPFeasible I L x x' lam f →
      128 * Real.logb 2 (2 * (I.k : ℝ)) ≤ (ρ : ℝ) →
      ∀ 𝒞 : Set (AGroup (auxGraph lam)), AssignRun ρ (auxInit lam) 𝒞 →
      ∀ G ∈ 𝒞, ∀ i ∈ pairsOf G.C, ∀ b : Bool,
        ∃ F : List (List (Fin I.n) × ℝ), IsGroupFlow I L f G i b F ∧
          (F.map Prod.snd).sum = 1 ∧
          ∀ pw ∈ F, 0 ≤ pw.2 ∧ IsPathIn I.graph (I.term i b) (I.s G.zstar) pw.1 ∧
            (pEdges pw.1).length ≤ ρ ^ 2 * Ld I L) ∧
    ∃ C : ℝ, ∀ k L : ℕ,
      (((⌈128 * Real.logb 2 (2 * (k : ℝ))⌉₊ ^ 2 * ((1 + Nat.log 2 k) * L) : ℕ)) : ℝ) ≤
        C * Real.log ((k : ℝ) + 1) ^ 3 * (L : ℝ) := by sorry

end MCPoise
