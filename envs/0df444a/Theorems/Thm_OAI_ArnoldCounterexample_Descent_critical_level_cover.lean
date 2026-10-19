-- Prove2me | Theorems.Thm_OAI_ArnoldCounterexample_Descent_critical_level_cover
-- name    : OAI.ArnoldCounterexample.Descent.critical_level_cover
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T09:23:14.643479+00:00
-- url     : https://prove2.me/theorems/299af0a4-feeb-497d-ac99-08c8a6d7dab9
-- title:
--   Critical-value cover: a sublevel set is covered by as many iterated chart preimages as there are critical values
-- statement:
--   Let $X$ be a compact topological space, $D:X\to X$, $f:X\to\mathbb{R}$ and $\ell:X\to\mathbb{C}$ continuous. Assume:
--
--   1. $f(Dx)\le f(x)$ for all $x$ (Lyapunov property);
--   2. $f(Dx)<f(x)$ whenever $\ell(x)=0$;
--   3. for a finite set $s\subset\mathbb{R}$ and a level $a$: every $x$ with $f(x)\le a$ and $f(Dx)=f(x)$ has $f(x)\in s$.
--
--   Then there is a finite set $T\subseteq\mathbb{N}$ with $|T|\le|s|$ such that
--   $$
--   f(x)\le a\ \Longrightarrow\ \exists\,n\in T:\ \ell\bigl(D^nx\bigr)\neq0 .
--   $$
--
--   In words: $\{f\le a\}$ is covered by at most $|s|$ sets of the form $D^{-n}\{\ell\ne0\}$, each the preimage, under an iterate of the single descent map $D$, of the region where the coordinate $\ell$ is nonzero. This is a Lusternik–Schnirelmann-type estimate: the number of critical values bounds the size of such covers, and topology then forces enough critical values.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/Arnold/Descent.lean#L168-L244

import Mathlib
import Definitions.Def_ArnoldCounterexample
import Definitions.Def_OAI_Geometry_Arnold_Involution
import Definitions.Def_OAI_Geometry_Arnold_Projective
import Definitions.Def_OAI_Geometry_Arnold_Rotation
import Definitions.Def_OAI_Geometry_Arnold_Tangent
import Definitions.Def_OAI_Geometry_Arnold_Haar
import Definitions.Def_OAI_Geometry_Arnold_Differentiation
import Definitions.Def_OAI_Geometry_Arnold_Orbit
import Definitions.Def_OAI_Geometry_Arnold_Symplectic
import Definitions.Def_OAI_Geometry_Arnold_Coordinates
import Definitions.Def_OAI_Geometry_Arnold_Extension

open OAI OAI.ArnoldCounterexample
universe uE uX
open scoped BigOperators ContDiff
open MeasureTheory Set Filter
open scoped Matrix.Norms.Operator
open scoped Topology
open Set
open scoped ContDiff
open Set Function
variable {X : Type uX} [TopologicalSpace X] [CompactSpace X]

theorem OAI.ArnoldCounterexample.Descent.critical_level_cover {D : X → X} {f : X → ℝ} {ℓ : X → ℂ}
    (hD : Continuous D) (hf : Continuous f) (hℓ : Continuous ℓ)
    (hdec : ∀ x, f (D x) ≤ f x)
    (hchart : ∀ x, ℓ x = 0 → f (D x) < f x)
    (s : Finset ℝ) (a : ℝ)
    (hstationary : ∀ x, f x ≤ a → f (D x) = f x → f x ∈ s) :
    ∃ T : Finset ℕ, T.card ≤ s.card ∧
      ∀ x, f x ≤ a → ∃ n ∈ T, ℓ (D^[n] x) ≠ 0 := by sorry
