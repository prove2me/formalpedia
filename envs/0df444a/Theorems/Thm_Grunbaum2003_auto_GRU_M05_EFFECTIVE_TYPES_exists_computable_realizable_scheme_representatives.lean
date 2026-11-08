-- Prove2me | Theorems.Thm_Grunbaum2003_auto_GRU_M05_EFFECTIVE_TYPES_exists_computable_realizable_scheme_representatives
-- name    : Grunbaum2003.auto_GRU_M05_EFFECTIVE_TYPES_exists_computable_realizable_scheme_representatives
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-10-31T22:21:37.871798+00:00
-- url     : https://prove2.me/theorems/97afb87a-c1c4-48db-a4fa-1a449818610a
-- title:
--   Computable Tarski–Seidenberg enumeration of canonical realizable vertex-face schemes (M05)
-- statement:
--   This lemma states the algorithmic Tarski–Seidenberg quantifier-elimination step of Grünbaum's Theorem 5.5.2 for the `GRU_M05_EFFECTIVE_TYPES` package: there exists a computable two-argument function $E(d, k)$ enumerating a canonical representative list of realizable vertex-face incidence schemes on $k$ vertices in $\mathbb{R}^d$.
--
--   Specifically, there exists a computable function $E : \mathbb{N} \to \mathbb{N} \to \operatorname{List}(\operatorname{List}(\operatorname{List} \mathbb{N}))$ (`Computable₂ E`) such that for every dimension $d \in \mathbb{N}$ and vertex count $k \in \mathbb{N}$:
--
--   1. Every scheme $S \in E(d, k)$ is realized by some $d$-polytope $P \subseteq \mathbb{R}^d$ (`SchemeRealizes k S P`);
--   2. For every realizable scheme $S_0$, there exists $S \in E(d, k)$ such that every polytope $P$ realizing $S_0$ also realizes $S$:
--
--   $$
--   \bigl(\exists P_0 \subseteq \mathbb{R}^d,\; \operatorname{SchemeRealizes}(k, S_0, P_0)\bigr) \implies \exists S \in E(d, k),\; \forall P \subseteq \mathbb{R}^d,\; \bigl(\operatorname{SchemeRealizes}(k, S_0, P) \implies \operatorname{SchemeRealizes}(k, S, P)\bigr);
--   $$
--
--   3. Distinct indices $i, j$ in $E(d, k)$ never realize polytopes with order-isomorphic face lattices.
--
--   Combined with the finite-scheme existence proof (that every $d$-polytope $P$ with $f_0(P) = k$ realizes some finite scheme $S_0$), this yields `auto_GRU_M05_EFFECTIVE_TYPES_combinatorial_types_effectively_enumerable`.
--
--   **Formalization Note** This declaration uses the `Def_auto_GRU_M05_EFFECTIVE_TYPES_*` definition modules required by the `auto_GRU_M05_EFFECTIVE_TYPES_combinatorial_types_effectively_enumerable` target.
-- source:
--   Grünbaum 2003, Convex Polytopes (2nd ed., Graduate Texts in Mathematics 221), §5.5, pp. 90–91, Theorem 5.5.2

import Definitions.Def_auto_GRU_M05_EFFECTIVE_TYPES_IsDPolytope
import Definitions.Def_auto_GRU_M05_EFFECTIVE_TYPES_PolytopeFace
import Definitions.Def_auto_GRU_M05_EFFECTIVE_TYPES_SchemeRealizes
import Mathlib.Computability.Partrec

set_option autoImplicit false

namespace Grunbaum2003

theorem auto_GRU_M05_EFFECTIVE_TYPES_exists_computable_realizable_scheme_representatives :
    ∃ E : ℕ → ℕ → List (List (List ℕ)), Computable₂ E ∧
      ∀ d k : ℕ,
        (∀ S ∈ E d k, ∃ P : Set (Fin d → ℝ), SchemeRealizes k S P) ∧
        (∀ S₀ : List (List ℕ), (∃ P₀ : Set (Fin d → ℝ), SchemeRealizes k S₀ P₀) →
          ∃ S ∈ E d k, ∀ P : Set (Fin d → ℝ), SchemeRealizes k S₀ P → SchemeRealizes k S P) ∧
        (∀ i j : Fin (E d k).length,
          ∀ P Q : Set (Fin d → ℝ),
            SchemeRealizes k ((E d k).get i) P →
            SchemeRealizes k ((E d k).get j) Q →
            Nonempty (PolytopeFace P ≃o PolytopeFace Q) → i = j) := by sorry

end Grunbaum2003
