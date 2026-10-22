-- Prove2me | Theorems.Thm_LieSuperCStar_Correspondence_proposition_3_2
-- name    : LieSuperCStar.Correspondence.proposition_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:33:33.685051+00:00
-- url     : https://prove2.me/theorems/0dbaadf9-a083-419e-a4ba-11542807db5c
-- title:
--   Proposition 3.2, p. 7 — uniform operator bound for represented generators
-- statement:
--   Let $(G,\mathfrak g)$ be a finite-dimensional Lie supergroup, $D=x_1\cdots x_k$ a word in its Lie superalgebra, and $f$ a smooth compactly supported test function on $G_\varepsilon$. There is a constant $M_{D,f}>0$, depending on $D$ and $f$ but independent of the unitary representation, such that
--
--   $$
--   \|\rho^\pi(D)\pi(f)\|\leq M_{D,f}
--   \quad\text{for every unitary }(\pi,\rho^\pi,\mathcal H).
--   $$
--
--   The estimate is what places every represented generator in the bounded universal product used to form $\mathcal A(G,\mathfrak g)$. A general element of $U(\mathfrak g_{\mathbb C})$ is a finite complex linear combination of words.
--
--   **Formalization Note** The bound is stated on every vector and every `Type`-small Hilbert representation. The vector integral defining $\pi(f)$ is used; no operator-norm Bochner integral is assumed.
-- source:
--   Neeb–Salmasian, C*-algebras and direct integral decomposition for Lie supergroups, arXiv:1506.01558v1, p. 7, Proposition 3.2

import Mathlib
import Definitions.Def_LieSuperCStar_Correspondence_Setting

noncomputable section
open MeasureTheory
open scoped Manifold ContDiff

namespace LieSuperCStar.Correspondence

/-- Proposition 3.2, p. 7: a bound independent of the unitary representation. -/
theorem proposition_3_2
    {E G F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G]
    [Group G] [LieGroup 𝓘(ℝ, E) ∞ G] [MeasurableSpace G] [BorelSpace G]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (hc : HCPair E G F) (μ : Measure G) [μ.IsHaarMeasure]
    (xs : List (SuperLie E G F)) (f : TestPair G)
    (hf₀ : IsTestFn (E := E) f.1) (hf₁ : IsTestFn (E := E) f.2) :
    ∃ M : ℝ, 0 < M ∧
      ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        (π : UnitaryRep hc H) (v : H),
        ‖genOp μ π xs f v‖ ≤ M * ‖v‖ := by sorry

end LieSuperCStar.Correspondence
