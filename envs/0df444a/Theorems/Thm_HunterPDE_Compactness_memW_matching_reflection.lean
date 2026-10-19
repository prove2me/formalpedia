-- Prove2me | Theorems.Thm_HunterPDE_Compactness_memW_matching_reflection
-- name    : HunterPDE.Compactness.memW_matching_reflection
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-16T09:08:04.71116+00:00
-- url     : https://prove2.me/theorems/64249917-a734-42e1-94ec-39ab5027aba9
-- title:
--   Finite reflected copies with matching moments preserve Sobolev regularity
-- statement:
--   Let $H_i=\{x\in\mathbb R^n:x_i>0\}$, $k\ge0$, and $1\le p<\infty$. Let $b_j>0$ and $c_j\in\mathbb R$ be finitely many dilation factors and coefficients satisfying
--   $$\sum_j c_j(-b_j)^r=1\qquad(0\le r\le k).$$
--   For $f\in W^{k,p}(H_i)$ define $Ef(x)=f(x)$ when $x_i>0$, and on the complementary half-space set
--   $$Ef(x)=\sum_j c_j f(x_1,\ldots,x_{i-1},-b_jx_i,x_{i+1},\ldots,x_n).$$
--   Then $Ef\in W^{k,p}(\mathbb R^n)$. No boundary values of $f$ are prescribed: changing the formula on the separating hyperplane has no effect on the assertion.
--
--   The moment identities match normal derivatives across the hyperplane. The substantive obligation is distributional gluing for arbitrary weak Sobolev data, together with integrability under the finitely many invertible normal dilations. A proof can use independent inward-translation smoothing and closure of weak derivatives, or direct boundary cancellation. It must not use density derived from this extension theorem.
-- source:
--   Sung-Jin Oh, Lecture Notes for Math 222A, March 19, 2024, proof of Proposition 11.13, Step 2, printed p. 158, equations (11.3)-(11.4), https://math.berkeley.edu/~sjoh/pdfs/notes-math222a.pdf . Whole-space weak Sobolev version of the matching-reflection construction, allowing any coordinate and arbitrary positive dilation factors. Passing from smooth data to weak Sobolev data remains part of this statement; it is not asserted to be proved by the displayed smooth calculation alone.

import Definitions.Def_HunterPDE_Compactness_Sobolev
open MeasureTheory
open scoped ENNReal
set_option autoImplicit false

theorem HunterPDE.Compactness.memW_matching_reflection
    {n : ℕ} (i : Fin n) (k N : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (b c : Fin N → ℝ) (hb : ∀ j, 0 < b j)
    (hc : ∀ r : ℕ, r ≤ k → ∑ j : Fin N, c j * (-b j) ^ r = 1)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : HunterPDE.Compactness.MemW k p {x | 0 < x i} f) :
    HunterPDE.Compactness.MemW k p Set.univ
      (fun x => if 0 < x i then f x else
        ∑ j : Fin N, c j * f (WithLp.toLp 2 (Function.update (fun l => x l) i (-b j * x i)))) := by sorry
