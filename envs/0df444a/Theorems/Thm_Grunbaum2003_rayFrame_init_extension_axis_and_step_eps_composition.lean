-- Prove2me | Theorems.Thm_Grunbaum2003_rayFrame_init_extension_axis_and_step_eps_composition
-- name    : Grunbaum2003.rayFrame_init_extension_axis_and_step_eps_composition
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-09T02:13:12.172187+00:00
-- url     : https://prove2.me/theorems/b61b91df-86a7-4053-bccc-e0a651d2f306
-- title:
--   Rank-$1$ boundary frame initialization, extension axis selection, and relocated `stepEpsProgram` composition
-- statement:
--   Let $d \ge 2$ and let $P = \{x \in \mathbb{R}^d : L_i(x) \le 1\}$ be a $d$-polytope with $0 \in \operatorname{int} P$ and ray oracle $\operatorname{oracle}$.
--
--   1. The finite set $V$ of exposed vertices of $P$ with $|V| = f_0(P)$ induces an equivalence $\operatorname{Fin}(f_0(P)) \simeq \{x : \operatorname{IsExposed} \mathbb{R} P \{x\}\}$.
--   2. Any uncertified vertex $v \in \operatorname{ext} Q(S)$ with $\operatorname{oracle}(v) \ne v$ satisfies $v \ne 0$, $p_0 := \operatorname{oracle}(v) \in \operatorname{bd} P \setminus \{0\}$, and $L_j(p_0) < 1$ for all $j \in S$, initializing the rank-$1$ boundary frame $v_1 = (p_0)$, $w_1 = (1)$.
--   3. At any boundary frame stage $1 \le r < d$ with $p = \sum_{i < r} w_i v_i \in \operatorname{bd} P$, there exist a coordinate axis $e_{i_{\mathrm{axis}}} \notin \operatorname{span}(\operatorname{range} v)$ and a coordinate $j_{\mathrm{coord}} \ne i_{\mathrm{axis}}$ with $p_{j_{\mathrm{coord}}} \ne 0$.
--   4. Relocated execution of `stepEpsProgram` after a prefix program `pre` preserves lower tape cells and query count while writing the step size
--
--   $$
--   \varepsilon = \frac{a\,\delta}{2(1 + a\,M + \delta)}.
--   $$
--
--   This theorem supplies the frame initialization, coordinate-axis selection, and step-size gadget composition for the facet-discovery loop.
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

set_option autoImplicit false
open scoped BigOperators Classical

namespace Grunbaum2003

theorem rayFrame_init_extension_axis_and_step_eps_composition (d : ℕ) (hd : 2 ≤ d) :
    (∀ {P : Set (Fin d → ℝ)},
      (∃ n : ℕ, Nonempty (Fin n ≃ PolytopeFace P)) →
      ∀ (V : Finset (Fin d → ℝ)),
        (V : Set (Fin d → ℝ)) = {x : Fin d → ℝ | IsExposed ℝ P {x}} →
        V.card = faceCount P 0 →
        ∃ (n : ℕ) (_e : Fin n ≃ PolytopeFace P)
          (vEnum : Fin (faceCount P 0) ≃ {x : Fin d → ℝ | IsExposed ℝ P {x}}),
          ∀ k : Fin (faceCount P 0), (vEnum k).val ∈ V) ∧
    (∀ {m : ℕ} {P : Set (Fin d → ℝ)}, IsDPolytope P → (0 : Fin d → ℝ) ∈ interior P →
      ∀ (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ),
        P = {x | ∀ i, L i x ≤ 1} →
        ∀ {oracle : (Fin d → ℝ) → (Fin d → ℝ)}, IsPolytopeRayOracle P oracle →
          ∀ (S : Finset (Fin m)) {v : Fin d → ℝ},
            v ∈ ({x : Fin d → ℝ | ∀ i ∈ S, L i x ≤ 1}).extremePoints ℝ →
            oracle v ≠ v →
            let p₀ := oracle v
            let v₁ : Fin 1 → Fin d → ℝ := fun _ => p₀
            let w₁ : Fin 1 → ℝ := fun _ => 1
            v ≠ 0 ∧ p₀ ≠ 0 ∧ p₀ ∈ P ∧ p₀ ∈ frontier P ∧
              LinearIndependent ℝ v₁ ∧
              (∀ i : Fin 1, 0 < w₁ i) ∧
              (∑ i : Fin 1, w₁ i = 1) ∧
              p₀ = ∑ i : Fin 1, w₁ i • v₁ i ∧
              (∀ i : Fin 1, v₁ i ∈ P) ∧
              (∀ j ∈ S, L j p₀ < 1) ∧
              (∀ k : Fin m, L k p₀ = 1 → ∀ i : Fin 1, L k (v₁ i) = 1)) ∧
    (∀ {r : ℕ} {P : Set (Fin d → ℝ)}, (0 : Fin d → ℝ) ∈ interior P →
      ∀ (v : Fin r → Fin d → ℝ), LinearIndependent ℝ v → r < d →
        ∀ (w : Fin r → ℝ) (p : Fin d → ℝ),
          p ∈ frontier P → p = ∑ i : Fin r, w i • v i →
          ∃ (i_axis j_coord : Fin d),
            Pi.single i_axis (1 : ℝ) ∉ Submodule.span ℝ (Set.range v) ∧
            j_coord ≠ i_axis ∧
            p j_coord ≠ 0) ∧
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
       (stepEpsProgram : ℕ → ℕ → ℤ → ℤ → ℤ → ℤ → ℤ → List RayInstruction)
       (stepEpsDest : ℕ → ℕ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ)
       (stepEpsSteps : ℕ → ℕ → ℤ → ℤ → ℤ → ℤ → ℕ)
       (_hStepEpsProg : ∀ {k : ℕ} (oracle : (Fin d → ℝ) → Fin d → ℝ) (source : ℤ → ℝ)
          (rowBase pBase uBase aCell minBase : ℤ) (q : ℕ),
          0 < source aCell →
          (∀ j : Fin k,
            ∑ i : Fin d, source (rowBase + (j.val : ℤ) * (d : ℤ) + (i.val : ℤ)) *
              source (pBase + (i.val : ℤ)) < 1) →
          let prog := stepEpsProgram d k rowBase pBase uBase aCell minBase
          let dst := stepEpsDest d k rowBase pBase uBase aCell minBase
          let steps := stepEpsSteps d k rowBase pBase uBase aCell
          let rowVal (j : Fin k) (xBase : ℤ) : ℝ :=
            ∑ i : Fin d, source (rowBase + (j.val : ℤ) * (d : ℤ) + (i.val : ℤ)) *
              source (xBase + (i.val : ℤ))
          let δ : ℝ := ∏ j : Fin k, (1 - rowVal j pBase) / (1 + (1 - rowVal j pBase))
          let M : ℝ := 1 + ∑ j : Fin k, (rowVal j uBase) ^ 2
          minBase ≤ dst ∧
          ∃ c' : RayConfiguration,
            rayMachineRun prog oracle steps ⟨0, 0, source, q⟩ = some c' ∧
            c'.pc = steps ∧ prog[c'.pc]? = some .halt ∧
            c'.head = 0 ∧ c'.queries = q ∧
            c'.tape dst = source aCell * δ / (2 * (1 + source aCell * M + δ)) ∧
            ∀ z : ℤ, z < dst → c'.tape z = source z)
       {k : ℕ} (pre : List RayInstruction)
       (oracle : (Fin d → ℝ) → (Fin d → ℝ))
       (t_pre : ℕ) (c_pre : RayConfiguration) (rowBase pBase uBase aCell minBase : ℤ),
      rayMachineRun (pre ++
          (stepEpsProgram d k rowBase pBase uBase aCell minBase).map (relocateInst pre.length))
        oracle t_pre { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } =
          some (relocateCfg pre.length ⟨0, 0, c_pre.tape, c_pre.queries⟩) →
      0 < c_pre.tape aCell →
      (∀ j : Fin k,
        ∑ i : Fin d, c_pre.tape (rowBase + (j.val : ℤ) * (d : ℤ) + (i.val : ℤ)) *
          c_pre.tape (pBase + (i.val : ℤ)) < 1) →
      let prog := pre ++
        (stepEpsProgram d k rowBase pBase uBase aCell minBase).map (relocateInst pre.length)
      let dst := stepEpsDest d k rowBase pBase uBase aCell minBase
      let rowVal (j : Fin k) (xBase : ℤ) : ℝ :=
        ∑ i : Fin d, c_pre.tape (rowBase + (j.val : ℤ) * (d : ℤ) + (i.val : ℤ)) *
          c_pre.tape (xBase + (i.val : ℤ))
      let δ : ℝ := ∏ j : Fin k, (1 - rowVal j pBase) / (1 + (1 - rowVal j pBase))
      let M : ℝ := 1 + ∑ j : Fin k, (rowVal j uBase) ^ 2
      minBase ≤ dst ∧
      ∃ (t : ℕ) (c : RayConfiguration),
        rayMachineRun prog oracle t
          { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } = some c ∧
        prog[c.pc]? = some .halt ∧
        c.head = 0 ∧
        c.queries = c_pre.queries ∧
        c.tape dst = c_pre.tape aCell * δ / (2 * (1 + c_pre.tape aCell * M + δ)) ∧
        (∀ z : ℤ, z < dst → c.tape z = c_pre.tape z)) := by sorry

end Grunbaum2003
