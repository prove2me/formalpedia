-- Prove2me | Theorems.Thm_OAI_Paper256_pencil_compression_positive
-- name    : OAI.Paper256.pencil_compression_positive
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T19:06:28.936092+00:00
-- url     : https://prove2.me/theorems/efb5989d-4122-4540-a92c-36b809f4f8df
-- title:
--   Compressing a linear matrix pencil to one that is positive definite at a given point
-- statement:
--   Let $V$ be a real vector space (of any dimension). Write $\mathrm{Sym}_k$ for the real vector space of symmetric $k\times k$ real matrices. For a symmetric matrix $M$ write $M\succeq0$ if $M$ is positive semidefinite ($v^\top Mv\ge0$ for all real vectors $v$) and $M\succ0$ if it is positive definite ($v^\top Mv>0$ for all $v\neq0$). Let $L:V\to\mathrm{Sym}_n$ be a linear map and $e\in V$ a point such that
--
--   - $L(e)\succeq0$;
--   - the kernel of $L(e)$ is common to the whole pencil: for all $x\in V$ and $v\in\mathbb{R}^n$, $L(e)v=0$ implies $L(x)v=0$;
--   - the pencil is not everywhere positive semidefinite: there is $x\in V$ with $L(x)\not\succeq0$.
--
--   Then there exist an integer $m\ge1$ and a linear map $C:V\to\mathrm{Sym}_m$ such that
--   $$C(e)\succ0\qquad\text{and}\qquad L(x)\succeq0\iff C(x)\succeq0\quad\text{for all }x\in V .$$
--
--   In words, a spectrahedral description $\{x:L(x)\succeq0\}$ whose matrix at $e$ is positive semidefinite, with a kernel shared by all matrices of the pencil, can be replaced by a smaller description of the same set that is strictly positive at $e$; properness of the set guarantees that the new size is positive. This is the first normalization step when one assumes, for contradiction, that a cone with interior point $e$ is a spectrahedron.
--
--   **Formalization Note** $V$ is only an additive commutative group with a real module structure; no topology is used. Lean allows matrices of size $0$, which is why the conclusion records $0<m$ explicitly.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/HyperbolicCones/PencilCompression.lean#L54-L72

import Mathlib
import Definitions.Def_HyperbolicCones
import Definitions.Def_OAI_Analysis_HyperbolicCones_Model
import Definitions.Def_OAI_Analysis_HyperbolicCones_MatrixBasic
import Definitions.Def_OAI_Analysis_HyperbolicCones_MatrixLinear
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilConjugation

open OAI OAI.Paper256
open Matrix Set
open scoped Matrix.Norms.L2Operator
universe u
variable {V : Type u} [AddCommGroup V] [Module ℝ V]

theorem OAI.Paper256.pencil_compression_positive {n : ℕ} (L : V →ₗ[ℝ] Sym n) (e : V)
    (he : (L e : Mat n ℝ).PosSemidef)
    (hker : ∀ x : V, ∀ v : Fin n → ℝ,
      (L e : Mat n ℝ) *ᵥ v = 0 → (L x : Mat n ℝ) *ᵥ v = 0)
    (hproper : ∃ x : V, ¬(L x : Mat n ℝ).PosSemidef) :
    ∃ m : ℕ, 0 < m ∧ ∃ C : V →ₗ[ℝ] Sym m,
      (C e : Mat m ℝ).PosDef ∧
      ∀ x : V, (L x : Mat n ℝ).PosSemidef ↔ (C x : Mat m ℝ).PosSemidef := by sorry
