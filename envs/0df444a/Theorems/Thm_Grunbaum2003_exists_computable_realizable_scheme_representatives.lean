-- Prove2me | Theorems.Thm_Grunbaum2003_exists_computable_realizable_scheme_representatives
-- name    : Grunbaum2003.exists_computable_realizable_scheme_representatives
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-10-31T22:21:38.268256+00:00
-- url     : https://prove2.me/theorems/db06a42c-a9dc-43e4-a3df-c9b600318756
-- title:
--   Computable Tarski–Seidenberg enumeration of canonical realizable vertex-face schemes
-- statement:
--   This lemma isolates the algorithmic Tarski–Seidenberg quantifier-elimination step of Grünbaum's Theorem 5.5.2 (`combinatorial_types_effectively_enumerable`): there exists a computable two-argument function $E(d, k)$ that enumerates a duplicate-free list of canonical realizable vertex-face incidence schemes on $k$ vertices in $\mathbb{R}^d$.
--
--   Specifically, there exists a computable function $E : \mathbb{N} \to \mathbb{N} \to \operatorname{List}(\operatorname{List}(\operatorname{List} \mathbb{N}))$ (`Computable₂ E`) such that for every ambient dimension $d \in \mathbb{N}$ and vertex count $k \in \mathbb{N}$:
--
--   1. **Soundness:** Every scheme $S \in E(d, k)$ is geometrically realizable by some $d$-polytope $P \subseteq \mathbb{R}^d$:
--
--   $$
--   \forall S \in E(d, k),\quad \exists P \subseteq \mathbb{R}^d,\; \operatorname{SchemeRealizes}(k, S, P);
--   $$
--
--   2. **Completeness on realizable schemes:** For every realizable scheme $S_0$ on $k$ vertices in $\mathbb{R}^d$, there exists a representative $S \in E(d, k)$ such that every polytope $P$ realizing $S_0$ also realizes $S$ (under a suitable relabeling of its $k$ vertices);
--   3. **Irredundancy:** Distinct entries in $E(d, k)$ do not realize combinatorially equivalent polytopes.
--
--   Together with `exists_scheme_realizing_dpolytope` (which proves that every $d$-polytope $P$ with $f_0(P) = k$ realizes some finite scheme $S_0$), this lemma immediately yields `combinatorial_types_effectively_enumerable`.
--
--   **Formalization Note** Since there are only finitely many normalized schemes on $\{0, \dots, k-1\}$ and the existence of $V : \operatorname{Fin} k \to \mathbb{R}^d$ realizing a candidate scheme $S$ is a first-order sentence over the real closed field $(\mathbb{R}, +, \cdot, <)$, Tarski's decision procedure filters the finite candidate set to a canonical representative per combinatorial equivalence class.
-- source:
--   Grünbaum 2003, Convex Polytopes (2nd ed., Graduate Texts in Mathematics 221), §5.5, pp. 90–91, Theorem 5.5.2

import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_PolytopeFace
import Definitions.Def_Grunbaum2003_SchemeRealizes
import Mathlib.Computability.Partrec

set_option autoImplicit false

namespace Grunbaum2003

theorem exists_computable_realizable_scheme_representatives :
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
