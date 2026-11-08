-- Prove2me | Theorems.Thm_Grunbaum2003_rayMachine_planar_reference_walk_and_one_sided_budget
-- name    : Grunbaum2003.rayMachine_planar_reference_walk_and_one_sided_budget
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-07T18:41:29.538334+00:00
-- url     : https://prove2.me/theorems/382db218-06bb-4f99-86b8-72a6a8f5705c
-- title:
--   Planar reference-walk machine blocks, exit-prefix execution, terminal shared-support certificate, and $(2u+2)$ query budget
-- statement:
--   This theorem formalizes the complete planar secant reference-walk engine of the Gritzmann–Klee–Westwater ray-oracle algorithm on `rayMachineRun`, including its initialization programs, exit-prefix execution semantics, terminal shared-support certificate, and one-sided unknown-facet query budget:
--
--   1. **Planar initialization programs and native chord data (`secondQueryProgram_correct`, `firstMidpointProgram_correct`, `native_first_reference_data`):** At the normalized boundary anchor $p = (0, 1) \in \operatorname{frontier}(P)$, the first query along $r_1 = (-1, 1)$ returns $\operatorname{oracle}(r_1) = (-\tau, \tau)$ with $\tau > 0$. The 6-step `secondQueryProgram` queries $r_2(\tau) = (\frac{\tau}{1+\tau}, \frac{2}{1+\tau}) = p + B$, and the 12-step `firstMidpointProgram` queries $r_3(\tau) = \frac{1}{2}(p + r_2(\tau)) = p + \frac{1}{2} B$. The chord vector $B = r_2(\tau) - p$ satisfies $B_0 > 0$, $\operatorname{firstChordValue}(\tau, B) = 0$, $p - (1+\tau)B = \operatorname{oracle}(r_1) \in P$, and the convex affine gap $H(z) = \max_j \bigl(L_j(B) z + (L_j(p) - 1)\bigr)$ satisfies $H(0) = 0$ and $H(z) \ge 0$ for all $z \ge 0$.
--   2. **Exit-prefix execution and terminal shared-support certificate (`referenceWalkProgram_exits_of_first_guard`, `rayOracle_one_side_terminal_common_active`):** Any program matching `referenceWalkProgram` on instructions $0 \dots 26$ executes the scalar secant recurrence $x_{i+2} = \frac{x_{i+1} H(x_i) - x_i H(x_{i+1})}{H(x_i) - H(x_{i+1})}$ on actual oracle replies. At the first index $n$ where either terminal guard fires ($H(x_{n+1}) = 0$ or $x_{n+2} = 0$), the machine reaches `pc = 27` in $27n + 23$ or $27n + 24$ steps with `queries = q + n` (making no query on the final iteration), and there exists an original defining row $L_j$ shared by $p$ and $\operatorname{oracle}(p + x_{n+1} B)$ ($L_j(p) = L_j(\operatorname{oracle}(p + x_{n+1} B)) = 1$).
--   3. **One-sided unknown-facet query budget (`one_side_actual_prefix_query_budget`):** Whenever all oracle replies along $[0, x_0]$ have strict slack $L_j < 1$ on a set of already known facet rows `known : Finset (Fin m)`, each of the $n + 1$ positive-gap samples $x_0, \dots, x_n$ activates an unknown row $j \notin \mathrm{known}$ at most twice (`third_secant_response_leaves_common_piece`), yielding $n + 1 \le 2(m - |\mathrm{known}|)$ and total phase query count $3 + n \le 2(m - |\mathrm{known}|) + 2$.
-- source:
--   Grünbaum 2003, Convex Polytopes (2nd ed., Graduate Texts in Mathematics 221), §3.6, pp. 52b–52c (citing Gritzmann–Klee–Westwater 1995)

import Definitions.Def_Grunbaum2003_IsPolytopeRayOracle
import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_RayInstruction
import Definitions.Def_Grunbaum2003_RayConfiguration
import Definitions.Def_Grunbaum2003_rayMachineStep
import Definitions.Def_Grunbaum2003_rayMachineRun
import Mathlib.Analysis.Convex.Slope
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Nat.Find
import Mathlib.Order.Fin.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

set_option autoImplicit false

namespace Grunbaum2003

theorem rayMachine_planar_reference_walk_and_one_sided_budget :
    ∃ (suppliedPoint : Fin 2 → ℝ)
      (firstDirection : Fin 2 → ℝ)
      (secondDirection : ℝ → Fin 2 → ℝ)
      (firstMidpointDirection : ℝ → Fin 2 → ℝ)
      (firstChordValue : ℝ → (Fin 2 → ℝ) → ℝ)
      (nativeReferenceFunctional : ℝ → (Fin 2 → ℝ) →L[ℝ] ℝ)
      (nativeGap : ∀ {m : ℕ}, 0 < m → (Fin m → (Fin 2 → ℝ) →L[ℝ] ℝ) → (Fin 2 → ℝ) → ℝ → ℝ)
      (secondQueryProgram : List RayInstruction)
      (firstMidpointProgram : List RayInstruction)
      (referenceWalkProgram : List RayInstruction),
      suppliedPoint = (fun i => if i = 0 then 0 else 1) ∧
      firstDirection = (fun i => if i = 0 then -1 else 1) ∧
      (∀ t : ℝ, secondDirection t = fun i => if i = 0 then t / (1 + t) else 2 / (1 + t)) ∧
      (∀ t : ℝ, firstMidpointDirection t = (1 / 2 : ℝ) • (suppliedPoint + secondDirection t)) ∧
      (∀ (t : ℝ) (x : Fin 2 → ℝ), firstChordValue t x = (t - 1) * x 0 + t * x 1) ∧
      (∀ (oracle : (Fin 2 → ℝ) → Fin 2 → ℝ) (tape : ℤ → ℝ) (q : ℕ),
        0 < tape 1 →
        ∃ c : RayConfiguration,
          rayMachineRun secondQueryProgram oracle 6
            {pc := 0, head := 0, tape := tape, queries := q} = some c ∧
          secondQueryProgram[c.pc]? = some .halt ∧ c.head = 0 ∧ c.queries = q + 1 ∧
          (∀ i : Fin 2, c.tape (i.val : ℤ) = oracle (secondDirection (tape 1)) i) ∧
          c.tape 3 = tape 1 + 1) ∧
      (∀ (oracle : (Fin 2 → ℝ) → Fin 2 → ℝ) (tape : ℤ → ℝ) (q : ℕ),
        1 < tape 3 →
        ∃ c : RayConfiguration,
          rayMachineRun firstMidpointProgram oracle 12
            {pc := 0, head := 0, tape := tape, queries := q} = some c ∧
          firstMidpointProgram[c.pc]? = some .halt ∧ c.head = 0 ∧ c.queries = q + 1 ∧
          (∀ i : Fin 2, c.tape (i.val : ℤ) = oracle (firstMidpointDirection (tape 3 - 1)) i) ∧
          c.tape 5 = tape 0 ∧ c.tape 6 = tape 1 ∧ c.tape 3 = tape 3) ∧
      (∀ {m : ℕ} (hm : 0 < m) (L : Fin m → (Fin 2 → ℝ) →L[ℝ] ℝ)
        {P : Set (Fin 2 → ℝ)}, P = {q | ∀ j, L j q ≤ 1} →
        ∀ {oracle : (Fin 2 → ℝ) → (Fin 2 → ℝ)}, IsPolytopeRayOracle P oracle →
        suppliedPoint ∈ frontier P →
        let τ := oracle firstDirection 1
        let B := secondDirection τ - suppliedPoint
        let H := nativeGap hm L B
        0 < τ ∧ 0 < B 0 ∧ firstChordValue τ B = 0 ∧ H 0 = 0 ∧
          (∀ z : ℝ, 0 ≤ z → 0 ≤ H z) ∧
          oracle firstDirection = suppliedPoint - (1 + τ) • B ∧
          suppliedPoint - (1 + τ) • B ∈ P ∧
          suppliedPoint + (1 : ℝ) • B = secondDirection τ ∧
          firstMidpointDirection τ = suppliedPoint + (1 / 2 : ℝ) • B ∧
          (oracle (secondDirection τ) ≠ secondDirection τ → 0 < H 1)) ∧
      (∀ (program : List RayInstruction),
        (∀ k : ℕ, k < 27 → program[k]? = referenceWalkProgram[k]?) →
        ∀ {m : ℕ} (hm : 0 < m) (L : Fin m → (Fin 2 → ℝ) →L[ℝ] ℝ)
          {P : Set (Fin 2 → ℝ)}, P = {v | ∀ j, L j v ≤ 1} →
        ∀ {oracle : (Fin 2 → ℝ) → (Fin 2 → ℝ)}, IsPolytopeRayOracle P oracle →
        suppliedPoint ∈ frontier P →
        ∀ {t : ℝ}, 0 < t → ∀ (B : Fin 2 → ℝ),
        firstChordValue t B = 0 → B 0 ≠ 0 →
        ∀ (xs : ℕ → ℝ),
        (∀ i : ℕ, xs (i + 2) =
          (xs (i + 1) * nativeGap hm L B (xs i) - xs i * nativeGap hm L B (xs (i + 1))) /
            (nativeGap hm L B (xs i) - nativeGap hm L B (xs (i + 1)))) →
        0 < xs 1 → xs 1 < xs 0 →
        0 < nativeGap hm L B (xs 0) →
        (∀ w : ℝ, 0 ≤ w → w ≤ xs 0 → 0 ≤ nativeGap hm L B w) →
        ∀ (tape : ℤ → ℝ) (q : ℕ), tape 3 = t + 1 →
        tape 0 = oracle (suppliedPoint + xs 1 • B) 0 →
        tape 1 = oracle (suppliedPoint + xs 1 • B) 1 →
        tape 5 = oracle (suppliedPoint + xs 0 • B) 0 →
        tape 6 = oracle (suppliedPoint + xs 0 • B) 1 →
        ∀ (n : ℕ),
        (∀ i : ℕ, i < n → nativeGap hm L B (xs (i + 1)) ≠ 0 ∧ xs (i + 2) ≠ 0) →
        ((∀ (known : Finset (Fin m)),
            (∀ z : ℝ, 0 ≤ z → z ≤ xs 0 → ∀ j ∈ known, L j (oracle (suppliedPoint + z • B)) < 1) →
            n + 1 ≤ 2 * (m - known.card) ∧ 3 + n ≤ 2 * (m - known.card) + 2) ∧
          ((nativeGap hm L B (xs (n + 1)) = 0 ∨ xs (n + 2) = 0) →
            (∀ {a : ℝ}, 0 < a → suppliedPoint - a • B ∈ P →
              ∃ j : Fin m, L j suppliedPoint = 1 ∧ L j (oracle (suppliedPoint + xs (n + 1) • B)) = 1) ∧
            ∃ c : RayConfiguration,
              rayMachineRun program oracle
                (27 * n + (if nativeGap hm L B (xs (n + 1)) = 0 then 23 else 24))
                {pc := 0, head := 0, tape := tape, queries := q} = some c ∧
              c.pc = 27 ∧ c.head = 0 ∧ c.queries = q + n ∧
              c.tape 5 = oracle (suppliedPoint + xs n • B) 0 ∧
              c.tape 6 = oracle (suppliedPoint + xs n • B) 1 ∧
              c.tape 9 = oracle (suppliedPoint + xs (n + 1) • B) 0 ∧
              c.tape 10 = oracle (suppliedPoint + xs (n + 1) • B) 1 ∧
              c.tape 3 = t + 1 ∧
              (c.tape 16 = 0 ↔ nativeGap hm L B (xs (n + 1)) = 0) ∧
              (∀ i : Fin 2, c.tape (i.val : ℤ) = (suppliedPoint + xs (n + 2) • B) i) ∧
              (∀ j : ℤ, j < 0 ∨ 16 < j → c.tape j = tape j)))) := by sorry

end Grunbaum2003
