-- Prove2me | Theorems.Thm_Grunbaum2003_simplicial_polygon_steinitz_and_higher_g_theorem_core_conditions
-- name    : Grunbaum2003.simplicial_polygon_steinitz_and_higher_g_theorem_core_conditions
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-08T03:45:49.039871+00:00
-- url     : https://prove2.me/theorems/94e55500-fa7a-42d6-9188-47895b736312
-- title:
--   Core geometric face-count conditions for $2$-polytopes ($d=2$), simplicial $3$-polytopes ($d=3$), and higher simplicial $d$-polytopes ($d \ge 4$)
-- statement:
--   Given the proved vertex bounds, edge pairs, simplicial facet vertices, subface hull injectivity, bipartite double counting, $d$-simplex face counts, and $M_d$-column/$M$-sequence bridges, this theorem isolates the three pure geometric face-count conditions:
--   1. ($d = 2$): Every $2$-polytope $P \subseteq \mathbb{R}^2$ has $f_1(P) = f_0(P)$, and for every $n \in \mathbb{N}$ there is a $2$-polytope with $f_0(P) = n + 3$.
--   2. ($d = 3$): Every simplicial $3$-polytope $P \subseteq \mathbb{R}^3$ satisfies $f_0(P) + f_2(P) = f_1(P) + 2$ and $3f_2(P) = 2f_1(P)$, and for every $n \in \mathbb{N}$ there is a simplicial $3$-polytope with $f_0(P) = n + 4$.
--   3. ($d \ge 4$): Necessity and sufficiency of `IsMSequence (d / 2) g` on `(faceCount P j.val : ℤ)` ($j \in \operatorname{Fin} d$).
-- source:
--   Grünbaum 2003, Convex Polytopes (2nd ed., Graduate Texts in Mathematics 221), §10.6, pp. 198a–198b

import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_IsSimplicialDPolytope
import Definitions.Def_Grunbaum2003_PolytopeFace
import Definitions.Def_Grunbaum2003_faceCount
import Definitions.Def_Grunbaum2003_IsMSequence
import Definitions.Def_Grunbaum2003_gTheoremMatrix
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Hull
import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.AffineSpace.Independent
import Mathlib.Order.Interval.Finset.Nat

set_option autoImplicit false
open scoped BigOperators Classical

namespace Grunbaum2003

theorem simplicial_polygon_steinitz_and_higher_g_theorem_core_conditions
    (hVertexBound : ∀ (d : ℕ) (P : Set (Fin d → ℝ)),
      faceCount P 0 = {x : Fin d → ℝ | IsExposed ℝ P {x}}.ncard ∧
      (IsDPolytope P → d + 1 ≤ faceCount P 0))
    (hEdgePair : ∀ {d : ℕ} {P : Set (Fin d → ℝ)},
      ({x : Fin d → ℝ | IsExposed ℝ P {x}}.Finite ∧
        ∀ E : PolytopeFace P,
          E.val = convexHull ℝ (E.val ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}})) →
      ∀ (F : Set (Fin d → ℝ)), IsExposed ℝ P F →
        ((F.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ F).direction = 1) ↔
          ∃ a b : Fin d → ℝ,
            IsExposed ℝ P {a} ∧ IsExposed ℝ P {b} ∧ a ≠ b ∧
            F ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}} = {a, b} ∧
            F = convexHull ℝ ({a, b} : Set (Fin d → ℝ))))
    (hSimplicialFacets : ∀ {d : ℕ} {P : Set (Fin d → ℝ)},
      IsSimplicialDPolytope P →
      ({x : Fin d → ℝ | IsExposed ℝ P {x}}.Finite ∧
        ∀ E : PolytopeFace P,
          E.val = convexHull ℝ (E.val ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}})) →
      ∀ (F : Set (Fin d → ℝ)), F.Nonempty → IsExposed ℝ P F →
        Module.finrank ℝ (affineSpan ℝ F).direction + 1 = d →
        ∃ v : Fin d → Fin d → ℝ,
          AffineIndependent ℝ v ∧
          Function.Injective v ∧
          (∀ i : Fin d, IsExposed ℝ P {v i}) ∧
          F = convexHull ℝ (Set.range v) ∧
          F ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}} = Set.range v ∧
          (F ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}}).ncard = d)
    (hDoubleCount :
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
        3 * ℱ.card = 2 * ℰ.card))
    (hSimplex :
      (∀ (d : ℕ) (v : Fin (d + 1) → Fin d → ℝ),
        AffineIndependent ℝ v →
        IsSimplicialDPolytope (convexHull ℝ (Set.range v)) ∧
        ∀ k : ℕ, faceCount (convexHull ℝ (Set.range v)) k = Nat.choose (d + 1) (k + 1)) ∧
      (∀ d : ℕ,
        ∃ P : Set (Fin d → ℝ),
          IsSimplicialDPolytope P ∧
          ∀ k : ℕ, faceCount P k = Nat.choose (d + 1) (k + 1)))
    (hMSeqBridge :
      (∀ (d : ℕ) (k : Fin (d + 1)),
        gTheoremMatrix d 0 k.val = (Nat.choose (d + 1) k.val : ℤ)) ∧
      (∀ (d : ℕ) (g : ℕ → ℕ), g 0 = 1 →
        (∑ j ∈ Finset.range (d / 2 + 1), (g j : ℤ) * gTheoremMatrix d j 0) = 1) ∧
      (∀ (d : ℕ), 2 ≤ d → ∀ (g : ℕ → ℕ), g 0 = 1 →
        (∑ j ∈ Finset.range (d / 2 + 1), (g j : ℤ) * gTheoremMatrix d j 1) =
          (d + 1 : ℤ) + (g 1 : ℤ)) ∧
      (∀ m n : ℕ,
        IsMSequence m (fun j => if j = 0 then 1 else if j = 1 then n else 0)) ∧
      (∀ g : ℕ → ℕ, IsMSequence 1 g ↔ g 0 = 1) ∧
      (∀ d : ℕ,
        ∃ (P : Set (Fin d → ℝ)) (g : ℕ → ℕ),
          IsSimplicialDPolytope P ∧
          IsMSequence (d / 2) g ∧
          g 1 = 0 ∧
          (∀ j : Fin d, (faceCount P j.val : ℤ) =
            ∑ i ∈ Finset.range (d / 2 + 1),
              (g i : ℤ) * gTheoremMatrix d i j.succ.val))) :
    ((∀ P : Set (Fin 2 → ℝ), IsDPolytope P → faceCount P 1 = faceCount P 0) ∧
      (∀ n : ℕ, ∃ P : Set (Fin 2 → ℝ), IsDPolytope P ∧ faceCount P 0 = n + 3)) ∧
    ((∀ P : Set (Fin 3 → ℝ), IsSimplicialDPolytope P →
        faceCount P 0 + faceCount P 2 = faceCount P 1 + 2 ∧
        3 * faceCount P 2 = 2 * faceCount P 1) ∧
      (∀ n : ℕ, ∃ P : Set (Fin 3 → ℝ), IsSimplicialDPolytope P ∧ faceCount P 0 = n + 4)) ∧
    (∀ (d : ℕ), 4 ≤ d →
      (∀ P : Set (Fin d → ℝ), IsSimplicialDPolytope P →
        ∃ g : ℕ → ℕ, IsMSequence (d / 2) g ∧
          ∀ j : Fin d, (faceCount P j.val : ℤ) =
            ∑ i ∈ Finset.range (d / 2 + 1), (g i : ℤ) * gTheoremMatrix d i j.succ.val) ∧
      (∀ g : ℕ → ℕ, IsMSequence (d / 2) g →
        ∃ P : Set (Fin d → ℝ), IsSimplicialDPolytope P ∧
          ∀ j : Fin d, (faceCount P j.val : ℤ) =
            ∑ i ∈ Finset.range (d / 2 + 1), (g i : ℤ) * gTheoremMatrix d i j.succ.val)) := by sorry

end Grunbaum2003
