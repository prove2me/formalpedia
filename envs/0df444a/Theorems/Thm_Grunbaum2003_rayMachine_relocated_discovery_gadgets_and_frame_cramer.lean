-- Prove2me | Theorems.Thm_Grunbaum2003_rayMachine_relocated_discovery_gadgets_and_frame_cramer
-- name    : Grunbaum2003.rayMachine_relocated_discovery_gadgets_and_frame_cramer
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-09T01:53:51.241433+00:00
-- url     : https://prove2.me/theorems/b0c1b838-877a-4df0-ad57-7787c59e427d
-- title:
--   Relocated discovery gadgets and boundary frame Cramer identification
-- statement:
--   Let $d \ge 2$ and let $P = \{x \in \mathbb{R}^d : L_j(x) \le 1 \text{ for all } j < m\}$ be a $d$-polytope presented by normalized facet functionals $L_j$ with $S \subseteq \{0,\dots,m-1\}$ denoting the set of already-discovered facet indices.
--
--   1. Relocated execution of `cramerRowProgram`, `midpointVecProgram`, and `facetVertexIncidenceMatrixProgram` after a prefix program `pre` preserves lower tape cells and query counts while writing the Cramer normal row, midpoint vector, and $m \times V$ facet-vertex incidence matrix.
--   2. Whenever $v_1,\dots,v_n \in P$ are linearly independent with positive convex combination $p = \sum_{i=1}^n w_i v_i \in \operatorname{bd} P$ satisfying $L_j(p) < 1$ for all $j \in S$, and $q \in P \setminus \operatorname{span}(v_1,\dots,v_n)$ shares an active facet $L_{j_*}(p) = L_{j_*}(q) = 1$, the augmented frame $(q, v_1, \dots, v_n)$ is linearly independent and its midpoint $p' = \frac{1}{2}(p+q) \in \operatorname{bd} P$ preserves strict slack $L_j(p') < 1$ for all $j \in S$. At $n = d$, $\det(v) \ne 0$ and the Cramer normal row equals a fresh facet functional $L_{i_{\mathrm{new}}}$ with $i_{\mathrm{new}} \notin S$ and $L_{i_{\mathrm{new}}}(p_0) = 1$.
--
--   $$
--   \sum_{k=0}^{d-1} \frac{\det(v_{\text{col } k \leftarrow \mathbf{1}})}{\det(v)}\,x_k = L_{i_{\mathrm{new}}}(x), \qquad i_{\mathrm{new}} \notin S.
--   $$
--
--   This theorem packages the relocated machine gadget compositions together with the boundary frame extension and Cramer facet-normal identification step.
-- source:
--   Grünbaum 2003, Convex Polytopes (2nd ed.), §5.5; Gritzmann–Klee–Westwater 1995, §5.2–5.5

import Definitions.Def_Grunbaum2003_IsPolytopeRayOracle
import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_faceCount
import Definitions.Def_Grunbaum2003_PolytopeFace
import Definitions.Def_Grunbaum2003_RayInstruction
import Definitions.Def_Grunbaum2003_RayConfiguration
import Definitions.Def_Grunbaum2003_rayMachineStep
import Definitions.Def_Grunbaum2003_rayMachineRun
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.Hull
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

set_option autoImplicit false
open scoped BigOperators Matrix Classical

namespace Grunbaum2003

theorem rayMachine_relocated_discovery_gadgets_and_frame_cramer (d : ℕ) :
    (∀ (_run_add : ∀ (program : List RayInstruction)
          (oracle : (Fin d → ℝ) → Fin d → ℝ) (a b : ℕ) (c : RayConfiguration),
          rayMachineRun program oracle (a + b) c =
            (rayMachineRun program oracle a c).bind (rayMachineRun program oracle b))
       (relocateInst : ℕ → RayInstruction → RayInstruction)
       (relocateCfg : ℕ → RayConfiguration → RayConfiguration)
       (_hRelocate : ∀ (pre program : List RayInstruction)
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
              (relocateCfg pre.length c).pc]? = some .halt))
       (cramerRowProgram : ℕ → ℤ → ℤ → List RayInstruction)
       (cramerRowDest : ℕ → ℤ → ℤ → ℤ)
       (cramerRowSteps : ℕ → ℤ → ℕ)
       (_hCramerProg : ∀ (oracle : (Fin d → ℝ) → Fin d → ℝ) (source : ℤ → ℝ)
          (vBase minBase : ℤ) (q : ℕ),
          let v : Matrix (Fin d) (Fin d) ℝ :=
            fun i j => source (vBase + (i.val : ℤ) * (d : ℤ) + (j.val : ℤ))
          v.det ≠ 0 →
          let prog := cramerRowProgram d vBase minBase
          let outBase := cramerRowDest d vBase minBase
          let steps := cramerRowSteps d vBase
          minBase ≤ outBase ∧
          ∃ c' : RayConfiguration,
            rayMachineRun prog oracle steps ⟨0, 0, source, q⟩ = some c' ∧
            c'.pc = steps ∧ prog[c'.pc]? = some .halt ∧
            c'.head = 0 ∧ c'.queries = q ∧
            (∀ k : Fin d,
              c'.tape (outBase + (k.val : ℤ)) =
                (v.updateCol k (fun _ => 1)).det / v.det) ∧
            (∀ z : ℤ, z < outBase → c'.tape z = source z))
       (pre : List RayInstruction)
       (oracle : (Fin d → ℝ) → (Fin d → ℝ))
       (t_pre : ℕ) (c_pre : RayConfiguration) (vBase minBase : ℤ),
      rayMachineRun (pre ++
          (cramerRowProgram d vBase minBase).map (relocateInst pre.length))
        oracle t_pre { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } =
          some (relocateCfg pre.length ⟨0, 0, c_pre.tape, c_pre.queries⟩) →
      Matrix.det (fun i j : Fin d => c_pre.tape (vBase + (i.val : ℤ) * (d : ℤ) + (j.val : ℤ))) ≠ 0 →
      let prog := pre ++ (cramerRowProgram d vBase minBase).map (relocateInst pre.length)
      let outBase := cramerRowDest d vBase minBase
      let v : Matrix (Fin d) (Fin d) ℝ :=
        fun i j => c_pre.tape (vBase + (i.val : ℤ) * (d : ℤ) + (j.val : ℤ))
      minBase ≤ outBase ∧
      ∃ (t : ℕ) (c : RayConfiguration),
        rayMachineRun prog oracle t
          { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } = some c ∧
        prog[c.pc]? = some .halt ∧
        c.head = 0 ∧
        c.queries = c_pre.queries ∧
        (∀ k : Fin d,
          c.tape (outBase + (k.val : ℤ)) = (v.updateCol k (fun _ => 1)).det / v.det) ∧
        (∀ z : ℤ, z < outBase → c.tape z = c_pre.tape z)) ∧
    (∀ (_run_add : ∀ (program : List RayInstruction)
          (oracle : (Fin d → ℝ) → Fin d → ℝ) (a b : ℕ) (c : RayConfiguration),
          rayMachineRun program oracle (a + b) c =
            (rayMachineRun program oracle a c).bind (rayMachineRun program oracle b))
       (relocateInst : ℕ → RayInstruction → RayInstruction)
       (relocateCfg : ℕ → RayConfiguration → RayConfiguration)
       (_hRelocate : ∀ (pre program : List RayInstruction)
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
              (relocateCfg pre.length c).pc]? = some .halt))
       (midpointVecProgram : ℕ → ℤ → ℤ → ℤ → List RayInstruction)
       (midpointVecDest : ℕ → ℤ → ℤ → ℤ → ℤ)
       (midpointVecSteps : ℕ → ℤ → ℤ → ℕ)
       (_hMidpointProg : ∀ (oracle : (Fin d → ℝ) → Fin d → ℝ) (source : ℤ → ℝ)
          (pBase qBase minBase : ℤ) (q : ℕ),
          let prog := midpointVecProgram d pBase qBase minBase
          let outBase := midpointVecDest d pBase qBase minBase
          let steps := midpointVecSteps d pBase qBase
          minBase ≤ outBase ∧
          ∃ c' : RayConfiguration,
            rayMachineRun prog oracle steps ⟨0, 0, source, q⟩ = some c' ∧
            c'.pc = steps ∧ prog[c'.pc]? = some .halt ∧
            c'.head = 0 ∧ c'.queries = q ∧
            (∀ i : Fin d,
              c'.tape (outBase + (i.val : ℤ)) =
                (source (pBase + (i.val : ℤ)) + source (qBase + (i.val : ℤ))) / 2) ∧
            (∀ z : ℤ, z < outBase → c'.tape z = source z))
       (pre : List RayInstruction)
       (oracle : (Fin d → ℝ) → (Fin d → ℝ))
       (t_pre : ℕ) (c_pre : RayConfiguration) (pBase qBase minBase : ℤ),
      rayMachineRun (pre ++
          (midpointVecProgram d pBase qBase minBase).map (relocateInst pre.length))
        oracle t_pre { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } =
          some (relocateCfg pre.length ⟨0, 0, c_pre.tape, c_pre.queries⟩) →
      let prog := pre ++ (midpointVecProgram d pBase qBase minBase).map (relocateInst pre.length)
      let outBase := midpointVecDest d pBase qBase minBase
      minBase ≤ outBase ∧
      ∃ (t : ℕ) (c : RayConfiguration),
        rayMachineRun prog oracle t
          { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } = some c ∧
        prog[c.pc]? = some .halt ∧
        c.head = 0 ∧
        c.queries = c_pre.queries ∧
        (∀ i : Fin d,
          c.tape (outBase + (i.val : ℤ)) =
            (c_pre.tape (pBase + (i.val : ℤ)) + c_pre.tape (qBase + (i.val : ℤ))) / 2) ∧
        (∀ z : ℤ, z < outBase → c.tape z = c_pre.tape z)) ∧
    (∀ (_run_add : ∀ (program : List RayInstruction)
          (oracle : (Fin d → ℝ) → Fin d → ℝ) (a b : ℕ) (c : RayConfiguration),
          rayMachineRun program oracle (a + b) c =
            (rayMachineRun program oracle a c).bind (rayMachineRun program oracle b))
       (relocateInst : ℕ → RayInstruction → RayInstruction)
       (relocateCfg : ℕ → RayConfiguration → RayConfiguration)
       (_hRelocate : ∀ (pre program : List RayInstruction)
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
              (relocateCfg pre.length c).pc]? = some .halt))
       (facetVertexIncidenceMatrixProgram : ℕ → ℕ → ℕ → ℤ → ℤ → ℤ → List RayInstruction)
       (facetVertexIncidenceMatrixDest : ℕ → ℕ → ℕ → ℤ → ℤ → ℤ → ℤ)
       (facetVertexIncidenceMatrixSteps : ℕ → ℕ → ℕ → ℤ → ℤ → ℕ)
       (facetVertexIncidenceMatrixPC : ℕ → ℕ → ℕ → ℤ → ℤ → ℕ)
       (_hIncMatrixProg : ∀ {m V : ℕ} (oracle : (Fin d → ℝ) → Fin d → ℝ) (source : ℤ → ℝ)
          (lBase xBase minBase : ℤ) (q : ℕ),
          let prog := facetVertexIncidenceMatrixProgram d m V lBase xBase minBase
          let outBase := facetVertexIncidenceMatrixDest d m V lBase xBase minBase
          let steps := facetVertexIncidenceMatrixSteps d m V lBase xBase
          let haltPC := facetVertexIncidenceMatrixPC d m V lBase xBase
          minBase ≤ outBase ∧
          ∃ c' : RayConfiguration,
            rayMachineRun prog oracle steps ⟨0, 0, source, q⟩ = some c' ∧
            c'.pc = haltPC ∧ prog[c'.pc]? = some .halt ∧
            c'.head = 0 ∧ c'.queries = q ∧
            (∀ (j : Fin m) (k : Fin V),
              c'.tape (outBase + (j.val : ℤ) * (V : ℤ) + (k.val : ℤ)) =
                if (∑ i : Fin d,
                    source (lBase + (j.val : ℤ) * (d : ℤ) + (i.val : ℤ)) *
                      source (xBase + (k.val : ℤ) * (d : ℤ) + (i.val : ℤ))) = 1
                then (1 : ℝ) else 0) ∧
            (∀ z : ℤ, z < outBase → c'.tape z = source z))
       {m V : ℕ} (pre : List RayInstruction)
       (oracle : (Fin d → ℝ) → (Fin d → ℝ))
       (t_pre : ℕ) (c_pre : RayConfiguration) (lBase xBase minBase : ℤ),
      rayMachineRun (pre ++
          (facetVertexIncidenceMatrixProgram d m V lBase xBase minBase).map (relocateInst pre.length))
        oracle t_pre { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } =
          some (relocateCfg pre.length ⟨0, 0, c_pre.tape, c_pre.queries⟩) →
      let prog := pre ++
        (facetVertexIncidenceMatrixProgram d m V lBase xBase minBase).map (relocateInst pre.length)
      let outBase := facetVertexIncidenceMatrixDest d m V lBase xBase minBase
      minBase ≤ outBase ∧
      ∃ (t : ℕ) (c : RayConfiguration),
        rayMachineRun prog oracle t
          { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } = some c ∧
        prog[c.pc]? = some .halt ∧
        c.head = 0 ∧
        c.queries = c_pre.queries ∧
        (∀ (j : Fin m) (k : Fin V),
          c.tape (outBase + (j.val : ℤ) * (V : ℤ) + (k.val : ℤ)) =
            if (∑ i : Fin d,
                c_pre.tape (lBase + (j.val : ℤ) * (d : ℤ) + (i.val : ℤ)) *
                  c_pre.tape (xBase + (k.val : ℤ) * (d : ℤ) + (i.val : ℤ))) = 1
            then (1 : ℝ) else 0) ∧
        (∀ z : ℤ, z < outBase → c.tape z = c_pre.tape z)) ∧
    (∀ {m : ℕ} {P : Set (Fin d → ℝ)} (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ),
      P = {x | ∀ j, L j x ≤ 1} →
      ∀ (S : Finset (Fin m)),
        (∀ {n : ℕ} (v : Fin n → Fin d → ℝ), LinearIndependent ℝ v →
          ∀ (w : Fin n → ℝ), (∀ i, 0 < w i) → (∑ i, w i = 1) →
          (∀ i, v i ∈ P) →
          ∀ (p q : Fin d → ℝ), p ∈ P → q ∈ P →
          p = ∑ i, w i • v i →
          (∀ j ∈ S, L j p < 1) →
          q ∉ Submodule.span ℝ (Set.range v) →
          ∀ (j_act : Fin m), L j_act p = 1 → L j_act q = 1 →
          let V : Fin (n + 1) → Fin d → ℝ := Fin.cons q v
          let W : Fin (n + 1) → ℝ := Fin.cons (1 / 2 : ℝ) (fun i => w i / 2)
          let p' := (1 / 2 : ℝ) • (p + q)
          LinearIndependent ℝ V ∧ (∀ i, 0 < W i) ∧ (∑ i, W i = 1) ∧
            p' = ∑ i, W i • V i ∧ (∀ i, V i ∈ P) ∧ p' ∈ frontier P ∧
            (∀ j ∈ S, L j p' < 1) ∧
            (∀ k : Fin m, L k p' = 1 → ∀ i, L k (V i) = 1)) ∧
        (∀ (v : Matrix (Fin d) (Fin d) ℝ), LinearIndependent ℝ v →
          ∀ (w : Fin d → ℝ), (∀ i, 0 < w i) → (∑ i, w i = 1) →
          (∀ i, v i ∈ P) →
          ∀ (p p₀ : Fin d → ℝ), p ∈ frontier P → p = ∑ i, w i • v i →
          (∀ j ∈ S, L j p < 1) →
          (∀ k : Fin m, L k p = 1 → L k p₀ = 1) →
          v.det ≠ 0 ∧ ∃ i_new : Fin m,
            i_new ∉ S ∧
            L i_new p₀ = 1 ∧
            ∀ x : Fin d → ℝ,
              ∑ k : Fin d, ((v.updateCol k (fun _ => 1)).det / v.det) * x k = L i_new x)) := by sorry

end Grunbaum2003
