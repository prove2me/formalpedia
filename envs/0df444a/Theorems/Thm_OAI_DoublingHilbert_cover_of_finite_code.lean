-- Prove2me | Theorems.Thm_OAI_DoublingHilbert_cover_of_finite_code
-- name    : OAI.DoublingHilbert.cover_of_finite_code
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T22:46:50.485171+00:00
-- url     : https://prove2.me/theorems/58d268db-34a4-4b21-9295-314e468fc04a
-- title:
--   A finite coding whose fibers have diameter less than $r$ yields at most $|I|$ centers in the set covering it at radius $r$
-- statement:
--   Let $(X,d)$ be a pseudometric space, let $s\subseteq X$ be any subset, let $I$ be a finite set and let $r$ be a real number. Suppose that $\kappa:s\to I$ is a coding of the points of $s$ whose fibers have diameter less than $r$, in the sense that
--
--   $$
--   \kappa(x)=\kappa(y)\ \Longrightarrow\ d(x,y)<r\qquad\text{for all } x,y\in s .
--   $$
--
--   Then there is a finite set $C\subseteq s$ with $|C|\le |I|$ such that every point of $s$ lies at distance less than $r$ from some point of $C$:
--
--   $$
--   \forall x\in s\ \ \exists y\in C:\quad d(x,y)<r .
--   $$
--
--   This is the elementary counting device behind intrinsic doubling estimates: to cover a set by few open balls of radius $r$ whose centers lie in the set itself, it suffices to attach to every point a code from a small finite alphabet so that points with equal codes are closer than $r$. No sign condition on $r$ is imposed (for nonempty $s$ the hypothesis, applied with $x=y$, already forces $r>0$).
--
--   **Formalization Note** The coding is a function on the subtype `s`, the bound is `Fintype.card I`, and the centers form a `Finset X` whose coercion is contained in `s`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/DoublingHilbert/Doubling.lean#L75-L98

import Mathlib
import Definitions.Def_DoublingHilbert
import Definitions.Def_OAI_Geometry_DoublingHilbert_Construction
import Definitions.Def_OAI_Geometry_DoublingHilbert_Derivatives
import Definitions.Def_OAI_Geometry_DoublingHilbert_Integration
import Definitions.Def_OAI_Geometry_DoublingHilbert_Rectangles
import Definitions.Def_OAI_Geometry_DoublingHilbert_Grids
import Definitions.Def_OAI_Geometry_DoublingHilbert_SelectedSheets
import Definitions.Def_OAI_Geometry_DoublingHilbert_Energy
import Definitions.Def_OAI_Geometry_DoublingHilbert_Crossings
import Definitions.Def_OAI_Geometry_DoublingHilbert_Doubling

open OAI OAI.DoublingHilbert
open MeasureTheory Set Filter
open scoped BigOperators Topology
open Set
open Set Metric

theorem OAI.DoublingHilbert.cover_of_finite_code {X I : Type*} [PseudoMetricSpace X] [Fintype I]
    (s : Set X) (code : s → I) {r : ℝ}
    (hcode : ∀ x y : s, code x = code y → dist (x : X) (y : X) < r) :
    ∃ centers : Finset X, centers.card ≤ Fintype.card I ∧
      (↑centers : Set X) ⊆ s ∧ ∀ x ∈ s, ∃ y ∈ centers, dist x y < r := by sorry
