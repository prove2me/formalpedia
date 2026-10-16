-- Prove2me | Theorems.Thm_HunterPDE_Compactness_exists_sobolev_extension_halfSpace
-- name    : HunterPDE.Compactness.exists_sobolev_extension_halfSpace
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-16T08:41:53.043216+00:00
-- url     : https://prove2.me/theorems/4242a73e-f84b-4809-8896-e64983dbe8ab
-- title:
--   Every finite-order half-space Sobolev function admits a whole-space extension
-- statement:
--   Let $H=\{x\in\mathbb R^{m+1}:x_{m+1}>0\}$, $k\in\mathbb N_0$, and $1\le p<\infty$. Every $f\in W^{k,p}(H)$ admits an extension $F\in W^{k,p}(\mathbb R^{m+1})$ satisfying
--   $$F=f\quad\text{almost everywhere on }H.$$
--
--   This is the extension step in Hunter's approximation argument preceding Theorem 3.42. It asserts only existence, with no chosen extension operator or norm bound. It includes order zero and arbitrary positive dimension. For higher orders, the extension must preserve all weak derivatives up to order $k$ across the boundary.
--
--   **Formalization Note.** The input uses the Compactness chapter's Sobolev predicate and the output uses the Sobolev chapter's predicate, so the extension is directly usable with the previously proved whole-space mollification and cutoff theorems. These predicates encode the same distributional Sobolev space using different multi-index presentations.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), p. 72, extension step preceding Theorem 3.42, https://math.ucdavis.edu/~hunter/pdes/pde_notes.pdf . Higher-order reflection construction: Sung-Jin Oh, Lecture Notes for Math 222A (updated 3/19/2024), proof of Proposition 11.13, Step 2, p. 158, equations (11.3)–(11.4), https://math.berkeley.edu/~sjoh/pdfs/notes-math222a.pdf . This is the half-space existence consequence of that construction; not a claim that Hunter's W^{1,p} Theorem 3.41 alone covers higher orders.

import Definitions.Def_HunterPDE_Compactness_Sobolev
import Definitions.Def_HunterPDE_Compactness_HalfSpace
import Definitions.Def_HunterPDE_Sobolev_SobolevSpace
open MeasureTheory
open scoped ENNReal
set_option autoImplicit false

theorem HunterPDE.Compactness.exists_sobolev_extension_halfSpace (m k : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (f : EuclideanSpace ℝ (Fin (m + 1)) → ℝ)
    (hf : HunterPDE.Compactness.MemW k p (HunterPDE.Compactness.upperHalfSpace m) f) :
    ∃ F : EuclideanSpace ℝ (Fin (m + 1)) → ℝ,
      HunterPDE.Sobolev.MemW k p Set.univ F ∧
        F =ᵐ[volume.restrict (HunterPDE.Compactness.upperHalfSpace m)] f := by sorry
