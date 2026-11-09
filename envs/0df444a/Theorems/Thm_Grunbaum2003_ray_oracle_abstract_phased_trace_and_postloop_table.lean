-- Prove2me | Theorems.Thm_Grunbaum2003_ray_oracle_abstract_phased_trace_and_postloop_table
-- name    : Grunbaum2003.ray_oracle_abstract_phased_trace_and_postloop_table
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-09T01:27:34.945704+00:00
-- url     : https://prove2.me/theorems/67710d3c-71c2-4825-aa87-0e13cda54b35
-- title:
--   Abstract phased outer-polytope termination and post-loop face-inclusion table composition
-- statement:
--   Let $d \ge 2$. First, for every $d$-polytope $P = \{x \in \mathbb{R}^d : \forall i < m,\, L_i(x) \le 1\}$ with $0 \in \operatorname{int} P$, every ray oracle $\operatorname{oracle}$ for $P$, and every initial facet subset $S_0 \subseteq \operatorname{Fin} m$ for which $Q(S_0) = \{x \in \mathbb{R}^d : \forall i \in S_0,\, L_i(x) \le 1\}$ is compact, starting from $C_0 = \varnothing$ and $q_0 \le d + 1$ there exist the finite exposed vertex set $V$ of $P$ ($|V| = f_0(P)$), a phase count $N \in \mathbb{N}$, and sequences $(S_s, C_s, q_s)_{s \le N}$ such that each step $s < N$ either certifies an uncertified vertex $v \in \operatorname{ext} Q(S_s) \cap P \setminus C_s$ at query cost $\le 1$ or probes $v \in \operatorname{ext} Q(S_s)$ with $\operatorname{oracle}(v) \neq v$ and discovers a facet $L_{i_{\text{new}}}(\operatorname{oracle}(v)) = 1$ at query cost $\le 1 + (d - 1)(2(m - |S_s|) + 3)$, terminating with $Q(S_N) = P$ and $C_N = V$. Second, any prefix program `pre` that produces the $n \times V$ face-vertex incidence table at `fvBase` for a vertex enumeration `vEnum : Fin V ≃ {x | IsExposed ℝ P {x}}` and face enumeration `e : Fin n ≃ PolytopeFace P` chains via `run_add` and `hRelocate` with `headerAndInclusionTableProgram` to halt in `c_pre.queries` total queries with the $1^n 0$ header and $n \times n$ face-inclusion table of $P$.
--
--   **Formalization Note** Outer-polytope completion $Q(S_N) = P$ and $C_N = V$ from $\operatorname{ext} Q(S_N) \subseteq C_N \subseteq \operatorname{ext} P$ follows from the Krein–Milman theorem (`closure_convexHull_extremePoints`).
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

theorem ray_oracle_abstract_phased_trace_and_postloop_table (d : ℕ) (hd : 2 ≤ d) :
    (∀ {m : ℕ} {P : Set (Fin d → ℝ)}, IsDPolytope P → (0 : Fin d → ℝ) ∈ interior P →
      ∀ (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ),
        P = {x : Fin d → ℝ | ∀ i : Fin m, L i x ≤ 1} →
        ∀ {oracle : (Fin d → ℝ) → (Fin d → ℝ)}, IsPolytopeRayOracle P oracle →
          ∃ (V : Finset (Fin d → ℝ))
            (N : ℕ)
            (S_seq : ℕ → Finset (Fin m))
            (C_seq : ℕ → Finset (Fin d → ℝ))
            (q_seq : ℕ → ℕ),
            (V : Set (Fin d → ℝ)) = P.extremePoints ℝ ∧
            (V : Set (Fin d → ℝ)) = {x : Fin d → ℝ | IsExposed ℝ P {x}} ∧
            V.card = faceCount P 0 ∧
            C_seq 0 = ∅ ∧
            q_seq 0 ≤ d + 1 ∧
            (∀ s < N,
              (S_seq (s + 1) = S_seq s ∧
                ∃ v ∈ ({x : Fin d → ℝ | ∀ i ∈ S_seq s, L i x ≤ 1}).extremePoints ℝ,
                  v ∈ P ∧ v ∉ C_seq s ∧ C_seq (s + 1) = insert v (C_seq s) ∧
                  q_seq (s + 1) ≤ q_seq s + 1) ∨
              (C_seq (s + 1) = C_seq s ∧
                ∃ v ∈ ({x : Fin d → ℝ | ∀ i ∈ S_seq s, L i x ≤ 1}).extremePoints ℝ,
                  oracle v ≠ v ∧
                  ∃ i_new : Fin m,
                    L i_new (oracle v) = 1 ∧
                    S_seq (s + 1) = insert i_new (S_seq s) ∧
                    q_seq (s + 1) ≤ q_seq s +
                      (1 + (d - 1) * (2 * (m - (S_seq s).card) + 3)))) ∧
            {x : Fin d → ℝ | ∀ i ∈ S_seq N, L i x ≤ 1} = P ∧
            C_seq N = V) ∧
    (∀ (run_add : ∀ (program : List RayInstruction)
          (oracle : (Fin d → ℝ) → Fin d → ℝ) (a b : ℕ) (c : RayConfiguration),
          rayMachineRun program oracle (a + b) c =
            (rayMachineRun program oracle a c).bind (rayMachineRun program oracle b))
       (relocateInst : ℕ → RayInstruction → RayInstruction)
       (relocateCfg : ℕ → RayConfiguration → RayConfiguration),
      (∀ (pre program : List RayInstruction)
        (oracle : (Fin d → ℝ) → (Fin d → ℝ)) (t : ℕ) (c : RayConfiguration),
        (relocateCfg pre.length c).pc = pre.length + c.pc ∧
        (relocateCfg pre.length c).head = c.head ∧
        (relocateCfg pre.length c).tape = c.tape ∧
        (relocateCfg pre.length c).queries = c.queries ∧
        rayMachineRun (pre ++ program.map (relocateInst pre.length)) oracle t
            (relocateCfg pre.length c) =
          (rayMachineRun program oracle t c).map (relocateCfg pre.length) ∧
        (program[c.pc]? = some .halt →
          (pre ++ program.map (relocateInst pre.length))[
            (relocateCfg pre.length c).pc]? = some .halt)) →
      ∀ (headerAndInclusionTableProgram : ℕ → ℕ → ℤ → ℤ → List RayInstruction)
        (headerAndInclusionTableDest : ℕ → ℕ → ℤ → ℤ → ℤ)
        (headerAndInclusionTableSteps : ℕ → ℕ → ℤ → ℕ),
        (∀ {n V : ℕ} (oracle : (Fin d → ℝ) → Fin d → ℝ) (source : ℤ → ℝ)
          (fvBase minBase : ℤ) (q : ℕ) (inc : Fin n → Fin V → Prop),
          (∀ (a : Fin n) (k : Fin V),
            source (fvBase + (a.val : ℤ) * (V : ℤ) + (k.val : ℤ)) =
              if inc a k then (1 : ℝ) else 0) →
          let prog := headerAndInclusionTableProgram n V fvBase minBase
          let outBase := headerAndInclusionTableDest n V fvBase minBase
          let steps := headerAndInclusionTableSteps n V fvBase
          minBase ≤ outBase ∧
          ∃ c' : RayConfiguration,
            rayMachineRun prog oracle steps ⟨0, 0, source, q⟩ = some c' ∧
            c'.pc = steps ∧ prog[c'.pc]? = some .halt ∧
            c'.head = outBase ∧ c'.queries = q ∧
            (∀ i : Fin n, c'.tape (c'.head + (i.val : ℤ)) = 1) ∧
            c'.tape (c'.head + (n : ℤ)) = 0 ∧
            (∀ i j : Fin n,
              c'.tape (c'.head + ((n + 1 + i.val * n + j.val : ℕ) : ℤ)) =
                if (∀ k : Fin V, inc i k → inc j k) then (1 : ℝ) else 0) ∧
            (∀ z : ℤ, z < c'.head → c'.tape z = source z)) →
        ∀ {P : Set (Fin d → ℝ)} {n V : ℕ}
          (vEnum : Fin V ≃ {x : Fin d → ℝ | IsExposed ℝ P {x}})
          (e : Fin n ≃ PolytopeFace P)
          (pre : List RayInstruction)
          (oracle : (Fin d → ℝ) → (Fin d → ℝ))
          (t_pre : ℕ) (c_pre : RayConfiguration) (fvBase minBase : ℤ),
          rayMachineRun (pre ++
              (headerAndInclusionTableProgram n V fvBase minBase).map (relocateInst pre.length))
            oracle t_pre { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } =
              some (relocateCfg pre.length ⟨0, 0, c_pre.tape, c_pre.queries⟩) →
          (∀ (a : Fin n) (k : Fin V),
            c_pre.tape (fvBase + (a.val : ℤ) * (V : ℤ) + (k.val : ℤ)) =
              if (vEnum k).val ∈ (e a).val then (1 : ℝ) else 0) →
          let prog := pre ++
            (headerAndInclusionTableProgram n V fvBase minBase).map (relocateInst pre.length)
          ∃ (t : ℕ) (c : RayConfiguration),
            rayMachineRun prog oracle t
              { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } = some c ∧
            prog[c.pc]? = some .halt ∧
            c.queries = c_pre.queries ∧
            (∀ i : Fin n, c.tape (c.head + (i.val : ℤ)) = 1) ∧
            c.tape (c.head + (n : ℤ)) = 0 ∧
            ∀ i j : Fin n,
              c.tape (c.head + ((n + 1 + i.val * n + j.val : ℕ) : ℤ)) =
                if (∀ x : Fin d → ℝ, IsExposed ℝ P {x} → x ∈ (e i).val → x ∈ (e j).val)
                then 1 else 0) := by sorry

end Grunbaum2003
