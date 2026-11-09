-- Prove2me | Theorems.Thm_KSPolySign_lemma_3_7_c
-- name    : KSPolySign.lemma_3_7_c
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:37:48.119105+00:00
-- url     : https://prove2.me/theorems/d6da2aa3-3f81-4b1b-8298-7fe408323b28
-- title:
--   Lemma 3.7(c) — the potential is $C^2$ on open faces and continuous on the cube
-- statement:
--   On each open face of the cube $[-1,1]^k$ (the points sharing the active set and the signed coordinates of some $y$), the primal variables $(b,U,V)$, the dual variables $(W,Z)$ and the potential $P$ are $C^2$ functions of the active coordinates with locally Lipschitz second derivatives. The potential $P$ is continuous on the closed cube.
--
--   This regularity makes the gradient and Hessian of $P$ in the active coordinates meaningful, and continuity gives a global minimizer of $P$ on the cube.
--
--   **Formalization Note** The open face of $y$ is parametrized by $O=\{x: |x_i|<1 \text{ for every active } i\}$ through $\mathrm{faceProj}(y,\cdot)$. "The primal and dual variables are $C^2$" is the existence of functions on $O$ giving at every point an optimizer and dual multipliers, each $C^2$ with locally Lipschitz second derivative (matrix-valued ones entrywise).
--
--   Differences from the source:
--   - generalization: the normalized inputs Ā_i of Lemma 3.1 (F = 0) → every maintained instance: PSD rank-one C_i with ∑C_i² ⪯ I, any Hermitian F, any ρ > 0; reason: Definition 3.5 evaluates this notation with C_i in place of Ā_i, and the normalized inputs are such an instance (ζ ≤ 1); the statement specializes to the source's
--   - encoding: matrices in ℂ^{n×n} with nonzero inputs (so n ≥ 1) → explicit hypothesis 1 ≤ n; reason: excludes only 0×0 matrices, where the program of Definition 3.3 is degenerate and P has no meaning
--   - reading: the primal and dual variables are C² with locally Lipschitz second derivatives on each open face → there are functions b, U, V, W, Z on the face giving an optimizer and dual multipliers at every point, each C² with locally Lipschitz iterated second derivative (matrix-valued entrywise); reason: the variables are the unique optimizer and multipliers (Lemma 3.7(a, b)) as functions of the point
-- source:
--   Z. Song, S. Yue, Polynomial Time Algorithms for the Kadison-Singer Problem, arXiv:2609.19794 (held version, sha256 47d4aaa5…), Lemma 3.7(c), p.20 (PDF p.20)

import Mathlib
import Definitions.Def_KSPolySign_IsOptimal
import Definitions.Def_KSPolySign_IsInstance
import Definitions.Def_KSPolySign_IsDualPair
import Definitions.Def_KSPolySign_faceFun
open Matrix
open scoped ComplexOrder

namespace KSPolySign

/-- **Lemma 3.7(c) (Regularity of the optimizer and the potential).** Song–Yue, *Polynomial Time Algorithms for the Kadison-Singer Problem*, arXiv:2609.19794 (held version, sha256 47d4aaa5…), Lemma 3.7(c), p.20 (PDF p.20).

On each open face of the cube, the primal and dual variables and `P` are `C²` with locally Lipschitz
second derivatives. `P` is continuous on the closed cube.

**Formalization Note** Stated for every maintained instance (Definition 3.5: nonzero PSD rank-one `C_i` with `∑ C_i² ⪯ I`, a fixed Hermitian `F`) and every `ρ > 0`; the normalized inputs are the case `F = 0`, `C_i = Ā_i`. `n ≥ 1` excludes `0 × 0` matrices. The open face of `y ∈ [−1, 1]^k` is parametrized by
`O = {x | |x_i| < 1 for every active i of y}` through `faceProj y`, which keeps the fixed coordinates
of `y`; a function on the face is a function of `x ∈ O`. "The primal and dual variables" are
functions `b, U, V, W, Z` on `O` that give, at every point, an optimizer and dual multipliers
(unique by Lemma 3.7(a, b)); the matrix-valued ones are `C²` with locally Lipschitz second derivative
entrywise. -/
theorem lemma_3_7_c (n k : ℕ) (hn : 1 ≤ n) (C : Fin k → Matrix (Fin n) (Fin n) ℂ) (hC : IsInstance C)
    (F : Matrix (Fin n) (Fin n) ℂ) (hF : F.IsHermitian) (ρ : ℝ) (hρ : 0 < ρ) :
    ContinuousOn (pot C F ρ) {x | ∀ i, |x i| ≤ 1} ∧
    ∀ y : Fin k → ℝ, (∀ i, |y i| ≤ 1) →
      let O : Set (Fin k → ℝ) := {x | ∀ i, |y i| < 1 → |x i| < 1}
      ∃ (bf : (Fin k → ℝ) → ℝ) (Uf Vf Wf Zf : (Fin k → ℝ) → Matrix (Fin n) (Fin n) ℂ),
        (∀ x ∈ O, IsOptimal C F ρ (faceProj y x) (bf x) (Uf x) (Vf x) ∧
          IsDualPair C ρ (faceProj y x) (Uf x) (Vf x) (Wf x) (Zf x)) ∧
        (ContDiffOn ℝ 2 (faceFun C F ρ y) O ∧ LocallyLipschitzOn O (iteratedFDeriv ℝ 2 (faceFun C F ρ y))) ∧
        (ContDiffOn ℝ 2 bf O ∧ LocallyLipschitzOn O (iteratedFDeriv ℝ 2 bf)) ∧
        ∀ G : (Fin k → ℝ) → Matrix (Fin n) (Fin n) ℂ, (G = Uf ∨ G = Vf ∨ G = Wf ∨ G = Zf) → ∀ a c : Fin n,
          ContDiffOn ℝ 2 (fun x => G x a c) O ∧ LocallyLipschitzOn O (iteratedFDeriv ℝ 2 (fun x => G x a c)) := by sorry

end KSPolySign
