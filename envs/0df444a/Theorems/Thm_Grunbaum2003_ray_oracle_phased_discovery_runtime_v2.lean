-- Prove2me | Theorems.Thm_Grunbaum2003_ray_oracle_phased_discovery_runtime_v2
-- name    : Grunbaum2003.ray_oracle_phased_discovery_runtime_v2
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-09T08:39:40.036677+00:00
-- url     : https://prove2.me/theorems/97c87334-cd13-44e4-b20c-73df5b8f0cfa
-- title:
--   Uniform ray discovery with actual execution traces (V2 specification)
-- statement:
--   For each dimension at least two, the target asks for one finite real ray-oracle program, independent of the input polytope, which reconstructs the complete face lattice with the bound
--
--   $$
--   q\leq f_0(P)+(d-1)f_{d-1}(P)^2+(5d-4)f_{d-1}(P).
--   $$
--
--   The input is any full-dimensional polytope containing zero in its interior, supplied only through its canonical ray oracle. The program starts with a blank tape. Its halted output must satisfy the unchanged canonical face-lattice format: a unary count of all faces, followed by the full Boolean inclusion matrix under a bijective face enumeration.
--
--   This version additionally requires a discovery trace linked to the actual execution. The program and one phase-control address are chosen before the polytope and oracle. Every milestone is the state reached at a specified, increasing execution time. The known normalized facet rows and certified vertices are represented by finite arrays on that state's tape; their counts and addresses occur in fixed control cells. The facet representation has exactly the actual number of facets, and distinct indices have distinct facet contact sets.
--
--   At the first milestone, both discovered sets are empty. Reaching this milestone costs at most d+1 actual queries. An initial containment segment discovers fresh facets until the outer halfspace intersection is compact. During this segment each designated query direction is nonzero and lies in the recession cone of the known halfspaces. Subsequent phases work with vertices of the bounded outer approximation.
--
--   Each phase has one of two forms:
--
--   1. A queried outer vertex is returned unchanged by the oracle, is added freshly to the certified set, and costs exactly one query.
--   2. A query produces a boundary point on a fresh facet, which is added to the known set without changing the certified set. Before containment this is a recession-direction query; afterwards it is an outer-vertex query whose response differs from that vertex. With m actual facets and k already known, the phase costs at most
--
--   $$
--   1+(d-1)\bigl(2(m-k)+3\bigr).
--   $$
--
--   Every designated query is witnessed by an actual query instruction at a time inside its phase, with the designated vector in its query cells. All costs are read from the actual machine query counters. There is no independently supplied budget sequence that could be set to zero.
--
--   At the final discovery milestone the outer approximation is the input polytope and the certified set is exactly its exposed-vertex set. Subsequent runtime computation produces the complete face/vertex incidence table and the canonical halted inclusion-table output. The table dimensions and addresses are data on tape. These postprocessing stages must use no further oracle queries.
--
--   This is a versioned replacement specification for the disproved leaf [ray_oracle_phased_discovery_loop_from_sector_and_budget](https://prove2.me/theorems/ff61873e-edc0-4145-acb9-a5e057125207). That leaf forced an input-dependent, unbounded output routine to be a suffix of one fixed finite program, and accepted abstract trace budgets unrelated to execution. This version retains a uniform finite program, replaces specialized output code by runtime data, and links every phase to its actual execution. It also makes the previously missing paid containment initialization explicit.
--
--   **Formalization Note.** This is an **open formalization target**, not a claim that a reconstruction algorithm has been implemented or proved. The exact original output condition and final query bound are retained; the literal machine semantics are unchanged. The phase organization refines Gritzmann–Klee–Westwater's containment and reconstruction framework. The tape layouts and refined phase-cost obligations are supplied here and are not claimed to be verbatim assertions from the source. Local checks of the schema, actual-query accounting, total-budget implication, and conditional refinement to the original root do not prove existence of a program satisfying this target.
-- source:
--   P. Gritzmann, V. Klee, J. Westwater, Polytope Containment and Determination by Linear Probes, Proc. London Math. Soc. (3) 70 (1995), 691–720, DOI https://doi.org/10.1112/plms/s3-70.3.691, §5.3–5.5, pp. 714–715. The runtime tape layouts and execution-coupled phase specification are a supplied versioned repair, not verbatim source declarations. Original reconstruction root: https://prove2.me/theorems/60ec78e9-77c6-458e-8d47-5b17e861648a. Disproved predecessor: https://prove2.me/theorems/ff61873e-edc0-4145-acb9-a5e057125207.

import Definitions.Def_Grunbaum2003_RayDiscoveryRuntimeV2

set_option autoImplicit false
open scoped Classical BigOperators

namespace Grunbaum2003

theorem ray_oracle_phased_discovery_runtime_v2 (d : ℕ) (hd : 2 ≤ d) :
    ∃ (program : List RayInstruction) (phasePC : ℕ),
      ∀ P : Set (Fin d → ℝ), IsDPolytope P → (0 : Fin d → ℝ) ∈ interior P →
        ∀ oracle : (Fin d → ℝ) → Fin d → ℝ, IsPolytopeRayOracle P oracle →
          ∃ (L : Fin (faceCount P (d - 1)) → (Fin d → ℝ) →L[ℝ] ℝ)
            (V : Finset (Fin d → ℝ)) (N boundedStart : ℕ)
            (S : ℕ → Finset (Fin (faceCount P (d - 1))))
            (C : ℕ → Finset (Fin d → ℝ))
            (time : ℕ → ℕ) (state : ℕ → RayConfiguration),
            P = {x | ∀ i, L i x ≤ 1} ∧
            (∀ i, {x ∈ P | L i x = 1}.Nonempty ∧
              IsExposed ℝ P {x ∈ P | L i x = 1} ∧
              Module.finrank ℝ (affineSpan ℝ {x ∈ P | L i x = 1}).direction = d - 1) ∧
            Function.Injective (fun i => {x ∈ P | L i x = 1}) ∧
            (V : Set (Fin d → ℝ)) = P.extremePoints ℝ ∧
            (V : Set (Fin d → ℝ)) = {x : Fin d → ℝ | IsExposed ℝ P {x}} ∧
            V.card = faceCount P 0 ∧
            S 0 = ∅ ∧ C 0 = ∅ ∧ (state 0).queries ≤ d + 1 ∧
            boundedStart ≤ N ∧
            (∀ s ≤ N,
              rayMachineRun program oracle (time s) RayV2.blank = some (state s) ∧
              (state s).pc = phasePC ∧ RayV2.DiscoveryTable L (S s) (C s) (state s)) ∧
            (∀ s < N, time s < time (s + 1)) ∧
            (∀ s, boundedStart ≤ s → s ≤ N → IsCompact (RayV2.outerApproximation L (S s))) ∧
            (∀ s < N,
              (boundedStart ≤ s ∧ S (s + 1) = S s ∧
                ∃ v ∈ (RayV2.outerApproximation L (S s)).extremePoints ℝ,
                  v ∉ C s ∧ oracle v = v ∧
                  RayV2.QueriedBetween program oracle (time s) (time (s + 1)) v ∧
                  C (s + 1) = insert v (C s) ∧
                  (state (s + 1)).queries = (state s).queries + 1) ∨
              (C (s + 1) = C s ∧
                ∃ (v : Fin d → ℝ) (i_new : Fin (faceCount P (d - 1))),
                  v ≠ 0 ∧ i_new ∉ S s ∧
                  (s < boundedStart → ∀ j ∈ S s, L j v ≤ 0) ∧
                  (boundedStart ≤ s →
                    v ∈ (RayV2.outerApproximation L (S s)).extremePoints ℝ ∧ oracle v ≠ v) ∧
                  RayV2.QueriedBetween program oracle (time s) (time (s + 1)) v ∧
                  L i_new (oracle v) = 1 ∧ S (s + 1) = insert i_new (S s) ∧
                  (state (s + 1)).queries ≤ (state s).queries +
                    (1 + (d - 1) * (2 * (faceCount P (d - 1) - (S s).card) + 3)))) ∧
            RayV2.outerApproximation L (S N) = P ∧ C N = V ∧
            ∃ (n : ℕ) (e : Fin n ≃ PolytopeFace P)
              (vEnum : Fin (faceCount P 0) ≃ {x : Fin d → ℝ | IsExposed ℝ P {x}})
              (tableTime haltTime : ℕ) (tableState haltState : RayConfiguration)
              (faceVertexBase : ℤ),
              time N ≤ tableTime ∧ tableTime ≤ haltTime ∧
              rayMachineRun program oracle tableTime RayV2.blank = some tableState ∧
              RayV2.FaceVertexTable e vEnum tableState faceVertexBase ∧
              rayMachineRun program oracle haltTime RayV2.blank = some haltState ∧
              program[haltState.pc]? = some .halt ∧
              tableState.queries = (state N).queries ∧
              haltState.queries = tableState.queries ∧
              haltState.queries ≤ faceCount P 0 + (d - 1) * (faceCount P (d - 1)) ^ 2 +
                (5 * d - 4) * faceCount P (d - 1) ∧
              IsRayFaceLatticeOutput P haltState := by sorry

end Grunbaum2003
