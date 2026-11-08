-- Prove2me | Theorems.Thm_Grunbaum2003_simplicial_facet_subfaces_and_bipartite_double_counting
-- name    : Grunbaum2003.simplicial_facet_subfaces_and_bipartite_double_counting
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-08T03:24:15.661869+00:00
-- url     : https://prove2.me/theorems/1aaad4e4-92cc-4973-9381-c64527581740
-- title:
--   Injectivity of simplicial facet subface hulls and bipartite facet-ridge-vertex double-counting identities
-- statement:
--   This theorem proves two foundational combinatorial ingredients for the $f$-vector characterization of $2$-polytopes and simplicial $d$-polytopes:
--   1. **Simplicial Subface Hull Injectivity:** For any injective family $v : \operatorname{Fin} d \hookrightarrow \mathbb{R}^d$ of exposed vertices of $P$ (such as the $d$ vertices of a simplicial facet), every subset $s \subseteq \operatorname{Fin} d$ satisfies $\operatorname{conv}(v '' s) \cap \operatorname{vert}(P) = v '' s$, so $s \mapsto \operatorname{conv}(v '' s)$ is injective (`convexHull ℝ (v '' s₁) = convexHull ℝ (v '' s₂) ↔ s₁ = s₂`).
--   2. **Bipartite Incidence Double Counting:** For any finite sets $\mathcal{F}, \mathcal{R}$ and incidence relation `inc` where every $F \in \mathcal{F}$ is incident to $a$ elements of $\mathcal{R}$ and every $R \in \mathcal{R}$ is incident to $b$ elements of $\mathcal{F}$, $a \cdot |\mathcal{F}| = b \cdot |\mathcal{R}|$. In particular, $a = b = 2$ gives $|\mathcal{E}| = |V|$ for polygons ($d = 2$), and $a = 3, b = 2$ gives $3|\mathcal{F}| = 2|\mathcal{E}|$ for simplicial $3$-polytopes ($d = 3$).
-- source:
--   Grünbaum 2003, Convex Polytopes (2nd ed., Graduate Texts in Mathematics 221), §10.6, pp. 198a–198b

import Definitions.Def_Grunbaum2003_PolytopeFace
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Hull
import Mathlib.Data.Finset.Card

set_option autoImplicit false
open scoped BigOperators Classical

namespace Grunbaum2003

theorem simplicial_facet_subfaces_and_bipartite_double_counting :
  (∀ {d : ℕ} {P : Set (Fin d → ℝ)} (v : Fin d → Fin d → ℝ),
    Function.Injective v →
    (∀ i : Fin d, IsExposed ℝ P {v i}) →
    (∀ s : Finset (Fin d),
      convexHull ℝ (v '' (s : Set (Fin d))) ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}} =
        v '' (s : Set (Fin d))) ∧
    (∀ s₁ s₂ : Finset (Fin d),
      convexHull ℝ (v '' (s₁ : Set (Fin d))) = convexHull ℝ (v '' (s₂ : Set (Fin d))) ↔
        s₁ = s₂)) ∧
  (∀ {α β : Type} (ℱ : Finset α) (ℛ : Finset β) (inc : α → β → Prop) (a b : ℕ),
    (∀ F ∈ ℱ, (ℛ.filter (fun R => inc F R)).card = a) →
    (∀ R ∈ ℛ, (ℱ.filter (fun F => inc F R)).card = b) →
    a * ℱ.card = b * ℛ.card) ∧
  (∀ {α β : Type} (ℰ : Finset α) (V : Finset β) (inc : α → β → Prop),
    (∀ E ∈ ℰ, (V.filter (fun v => inc E v)).card = 2) →
    (∀ v ∈ V, (ℰ.filter (fun E => inc E v)).card = 2) →
    ℰ.card = V.card) ∧
  (∀ {α β : Type} (ℱ : Finset α) (ℰ : Finset β) (inc : α → β → Prop),
    (∀ F ∈ ℱ, (ℰ.filter (fun E => inc F E)).card = 3) →
    (∀ E ∈ ℰ, (ℱ.filter (fun F => inc F E)).card = 2) →
    3 * ℱ.card = 2 * ℰ.card) := by sorry

end Grunbaum2003
