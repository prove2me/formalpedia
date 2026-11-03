-- Prove2me | Theorems.Thm_Grunbaum2003_exists_computable_scheme_representatives_of_realizability_decider
-- name    : Grunbaum2003.exists_computable_scheme_representatives_of_realizability_decider
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-02T07:15:30.766584+00:00
-- url     : https://prove2.me/theorems/8b047618-263f-4f6e-9e5f-6dd5c38f2703
-- title:
--   Computable combinatorial-type quotient pruning of vertex-face schemes from a realizability decider
-- statement:
--   This theorem reduces the construction of a computable enumerator $E(d, k)$ of irredundant, complete, realizable vertex-face scheme representatives (`exists_computable_scheme_representatives`) to the existence of a computable realizability decision procedure $D(d, k, S)$.
--
--   Suppose $D : \mathbb{N} \to \mathbb{N} \to \operatorname{List}(\operatorname{List} \mathbb{N}) \to \operatorname{Bool}$ is computable (`Computable (fun z => D z.1.1 z.1.2 z.2)`) and decides scheme realizability:
--   $$
--   \forall d, k, S,\quad D(d, k, S) = \mathrm{true} \iff \exists P \subseteq \mathbb{R}^d,\; \operatorname{SchemeRealizes}(k, S, P).
--   $$
--   Then there exists a computable binary function $E : \mathbb{N} \to \mathbb{N} \to \operatorname{List}(\operatorname{List}(\operatorname{List} \mathbb{N}))$ (`Computable₂ E`) such that for all $d, k \in \mathbb{N}$:
--   1. **Soundness:** Every scheme $S \in E(d, k)$ is realizable by some $d$-polytope $P \subseteq \mathbb{R}^d$;
--   2. **Completeness up to scheme equivalence:** For every realizable scheme $S_0$, there is a representative $S \in E(d, k)$ that realizes every polytope realized by $S_0$; and
--   3. **Pairwise non-isomorphism of face lattices:** Any two schemes $E(d, k)_i$ and $E(d, k)_j$ realizing polytopes $P$ and $Q$ with order-isomorphic face lattices (`Nonempty (PolytopeFace P ≃o PolytopeFace Q)`) satisfy $i = j$.
--
--   **Formalization Note** This theorem proves the entire finite candidate generation (`primrec_scheme_candidates`), face-poset isomorphism checker (`schemeTypeIsoCheck_iff_face_orderIso`), equivalence-class pruning (`pwFilter_complement_covers`, `pwFilter_complement_unique_indices`), and geometric transport (`schemeRealizes_transfer_all_of_face_orderIso`), isolating the Tarski–Seidenberg realizability decider $D$ as the sole remaining input.
-- source:
--   Grünbaum 2003, Convex Polytopes (2nd ed., Graduate Texts in Mathematics 221), §5.5, pp. 90–91, Theorem 5.5.2

import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_PolytopeFace
import Definitions.Def_Grunbaum2003_SchemeRealizes
import Theorems.Thm_Grunbaum2003_polytope_face_eq_convexHull_exposed_vertices
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Computability.Partrec
import Mathlib.Computability.Primrec.List
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Pairwise
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.Range
import Mathlib.Data.List.Sublists
import Mathlib.LinearAlgebra.Pi
import Mathlib.Order.Hom.Basic
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

set_option autoImplicit false

namespace Grunbaum2003

theorem exists_computable_scheme_representatives_of_realizability_decider
    (D : ℕ → ℕ → List (List ℕ) → Bool)
    (hDComp : Computable (fun z : (ℕ × ℕ) × List (List ℕ) => D z.1.1 z.1.2 z.2))
    (hDCorrect : ∀ d k S, D d k S = true ↔
      ∃ P : Set (Fin d → ℝ), SchemeRealizes k S P) :
    ∃ E : ℕ → ℕ → List (List (List ℕ)), Computable₂ E ∧
      ∀ d k : ℕ,
        (∀ S ∈ E d k, ∃ P : Set (Fin d → ℝ), SchemeRealizes k S P) ∧
        (∀ S₀ : List (List ℕ), (∃ P₀ : Set (Fin d → ℝ), SchemeRealizes k S₀ P₀) →
          ∃ S ∈ E d k, ∀ P : Set (Fin d → ℝ),
            SchemeRealizes k S₀ P → SchemeRealizes k S P) ∧
        (∀ i j : Fin (E d k).length, ∀ P Q : Set (Fin d → ℝ),
          SchemeRealizes k ((E d k).get i) P →
          SchemeRealizes k ((E d k).get j) Q →
          Nonempty (PolytopeFace P ≃o PolytopeFace Q) → i = j) := by sorry

end Grunbaum2003
