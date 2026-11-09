-- Prove2me | Theorems.Thm_Grunbaum2003_ray_oracle_outer_polytope_invariants_and_phased_trace_bound
-- name    : Grunbaum2003.ray_oracle_outer_polytope_invariants_and_phased_trace_bound
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-08T22:47:53.49573+00:00
-- url     : https://prove2.me/theorems/16c6d829-f2a2-4cc5-84dd-8d792480987e
-- title:
--   Outer-polytope invariants, extreme-point freshness, and potential-function query bound for phased ray-oracle reconstruction
-- statement:
--   Let $d \ge 2$ and let $P = \{x \in \mathbb{R}^d : \forall i < m,\, L_i(x) \le 1\}$ be a $d$-polytope with $0 \in \operatorname{int} P$ equipped with a ray oracle $\operatorname{oracle}$. For any subset $S \subseteq \{0, \dots, m-1\}$ of discovered facet indices, let $Q(S) = \{x \in \mathbb{R}^d : \forall i \in S,\, L_i(x) \le 1\}$ be the corresponding outer halfspace approximation. Then:
--
--   1. (**Extreme-to-exposed vertex identity and active-face characterization**) $\operatorname{ext} P = \{v \in \mathbb{R}^d : \{v\} \text{ is an exposed face of } P\}$, $f_0(P) = |\operatorname{ext} P|$, and for every exposed face $F$ of $P$ and facet index $i$, $F \subseteq \{x : L_i(x) = 1\}$ if and only if $L_i(v) = 1$ for every exposed vertex $v \in F$.
--   2. (**Outer-polytope persistence, fresh-facet discovery, and completion**) $P \subseteq Q(S)$, $P \cap \operatorname{ext} Q(S) \subseteq \operatorname{ext} P$, every failed extreme-point verification $v \in \operatorname{ext} Q(S)$ with $\operatorname{oracle}(v) \neq v$ and $L_{i_{\text{new}}}(\operatorname{oracle}(v)) = 1$ yields a fresh facet $i_{\text{new}} \notin S$, and once $Q(S) = \operatorname{conv}(V_Q)$ has $V_Q \subseteq C \subseteq \operatorname{ext} P$ and $\operatorname{ext} Q(S) \subseteq C$, we have $Q(S) = P$ and $C = \operatorname{ext} P$.
--   3. (**Phased trace query bound**) Any halting execution that begins with at most $d + 1$ initialization queries and executes $N$ phases—each either certifying an extreme point $v \in \operatorname{ext} Q(S_s) \cap P$ outside $C_s$ using at most $1$ query, or failing extreme-point verification on $v \in \operatorname{ext} Q(S_s)$ ($\operatorname{oracle}(v) \neq v$) and discovering a facet $L_{i_{\text{new}}}(\operatorname{oracle}(v)) = 1$ using at most $1 + (d - 1)(2(f_{d-1}(P) - |S_s|) + 3)$ queries—satisfies the total query bound
--
--   $$\operatorname{queries} \le f_0(P) + (d + 1) + \sum_{k=0}^{f_{d-1}(P)-1} \bigl(1 + (d - 1)(2(f_{d-1}(P) - k) + 3)\bigr).$$
--
--   **Formalization Note** Polytopes are represented by `IsDPolytope`, ray oracles by `IsPolytopeRayOracle`, and machine runs by `rayMachineRun`.
-- source:
--   Peter Gritzmann, Victor Klee, and Jeffrey Westwater, Polytope Containment and Determination by Linear Probes, Proc. London Math. Soc. (3) 70 (1995), §5.2 and §5.5, Theorem 5.18, pp. 715–720

import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_faceCount
import Definitions.Def_Grunbaum2003_IsPolytopeRayOracle
import Definitions.Def_Grunbaum2003_RayInstruction
import Definitions.Def_Grunbaum2003_RayConfiguration
import Definitions.Def_Grunbaum2003_rayMachineStep
import Definitions.Def_Grunbaum2003_rayMachineRun
import Definitions.Def_Grunbaum2003_PolytopeFace
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.Hull
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

set_option autoImplicit false
open scoped BigOperators Matrix Classical

namespace Grunbaum2003

theorem ray_oracle_outer_polytope_invariants_and_phased_trace_bound (d : ℕ) (hd : 2 ≤ d) :
    (∀ {m : ℕ} {P : Set (Fin d → ℝ)}, IsDPolytope P → (0 : Fin d → ℝ) ∈ interior P →
      ∀ (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ),
        P = {x : Fin d → ℝ | ∀ i : Fin m, L i x ≤ 1} →
        ∀ {oracle : (Fin d → ℝ) → (Fin d → ℝ)}, IsPolytopeRayOracle P oracle →
          (P.extremePoints ℝ = {x : Fin d → ℝ | IsExposed ℝ P {x}} ∧
            faceCount P 0 = (P.extremePoints ℝ).ncard) ∧
          (∀ (F : PolytopeFace P) (i : Fin m),
            F.val ⊆ {x : Fin d → ℝ | L i x = 1} ↔
              ∀ v : Fin d → ℝ, IsExposed ℝ P {v} → v ∈ F.val → L i v = 1) ∧
          (∀ S : Finset (Fin m),
            P ⊆ {x : Fin d → ℝ | ∀ i ∈ S, L i x ≤ 1} ∧
            P ∩ ({x : Fin d → ℝ | ∀ i ∈ S, L i x ≤ 1}).extremePoints ℝ ⊆ P.extremePoints ℝ ∧
            ∀ {v : Fin d → ℝ},
              v ∈ ({x : Fin d → ℝ | ∀ i ∈ S, L i x ≤ 1}).extremePoints ℝ →
              oracle v ≠ v →
              ∀ {i_new : Fin m}, L i_new (oracle v) = 1 →
                i_new ∉ S ∧ (insert i_new S).card = S.card + 1) ∧
          (∀ (S : Finset (Fin m)) (V_Q C : Set (Fin d → ℝ)),
            {x : Fin d → ℝ | ∀ i ∈ S, L i x ≤ 1} = convexHull ℝ V_Q →
            V_Q ⊆ C → C ⊆ P.extremePoints ℝ →
            ({x : Fin d → ℝ | ∀ i ∈ S, L i x ≤ 1}).extremePoints ℝ ⊆ C →
            {x : Fin d → ℝ | ∀ i ∈ S, L i x ≤ 1} = P ∧ C = P.extremePoints ℝ)) ∧
    (∀ (program : List RayInstruction) (P : Set (Fin d → ℝ)),
      IsDPolytope P → (0 : Fin d → ℝ) ∈ interior P →
      ∀ (oracle : (Fin d → ℝ) → (Fin d → ℝ)), IsPolytopeRayOracle P oracle →
        ∀ (L : Fin (faceCount P (d - 1)) → (Fin d → ℝ) →L[ℝ] ℝ),
          P = {x | ∀ i, L i x ≤ 1} →
          ∀ (t : ℕ) (c : RayConfiguration) (n : ℕ) (e : Fin n ≃ PolytopeFace P)
            (N : ℕ)
            (S_seq : ℕ → Finset (Fin (faceCount P (d - 1))))
            (C_seq : ℕ → Finset (Fin d → ℝ))
            (q_seq : ℕ → ℕ),
            rayMachineRun program oracle t
              { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } = some c →
            program[c.pc]? = some .halt →
            C_seq 0 = ∅ →
            q_seq 0 ≤ d + 1 →
            (∀ s < N,
              (S_seq (s + 1) = S_seq s ∧
                ∃ v ∈ ({x : Fin d → ℝ | ∀ i ∈ S_seq s, L i x ≤ 1}).extremePoints ℝ,
                  v ∈ P ∧ v ∉ C_seq s ∧ C_seq (s + 1) = insert v (C_seq s) ∧
                  q_seq (s + 1) ≤ q_seq s + 1) ∨
              (C_seq (s + 1) = C_seq s ∧
                ∃ v ∈ ({x : Fin d → ℝ | ∀ i ∈ S_seq s, L i x ≤ 1}).extremePoints ℝ,
                  oracle v ≠ v ∧
                  ∃ i_new : Fin (faceCount P (d - 1)),
                    L i_new (oracle v) = 1 ∧
                    S_seq (s + 1) = insert i_new (S_seq s) ∧
                    q_seq (s + 1) ≤ q_seq s +
                      (1 + (d - 1) * (2 * (faceCount P (d - 1) - (S_seq s).card) + 3)))) →
            c.queries ≤ q_seq N →
            (∀ i : Fin n, c.tape (c.head + (i.val : ℤ)) = 1) →
            c.tape (c.head + (n : ℤ)) = 0 →
            (∀ i j : Fin n,
              c.tape (c.head + ((n + 1 + i.val * n + j.val : ℕ) : ℤ)) =
                if (∀ x : Fin d → ℝ, IsExposed ℝ P {x} → x ∈ (e i).val → x ∈ (e j).val)
                then 1 else 0) →
            rayMachineRun program oracle t
              { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } = some c ∧
            program[c.pc]? = some .halt ∧
            c.queries ≤ faceCount P 0 + (d + 1) +
              ∑ k ∈ Finset.range (faceCount P (d - 1)),
                (1 + (d - 1) * (2 * (faceCount P (d - 1) - k) + 3)) ∧
            (∀ i : Fin n, c.tape (c.head + (i.val : ℤ)) = 1) ∧
            c.tape (c.head + (n : ℤ)) = 0 ∧
            ∀ i j : Fin n,
              c.tape (c.head + ((n + 1 + i.val * n + j.val : ℕ) : ℤ)) =
                if (∀ x : Fin d → ℝ, IsExposed ℝ P {x} → x ∈ (e i).val → x ∈ (e j).val)
                then 1 else 0) := by sorry

end Grunbaum2003
