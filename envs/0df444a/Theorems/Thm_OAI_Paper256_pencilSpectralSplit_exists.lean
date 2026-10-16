-- Prove2me | Theorems.Thm_OAI_Paper256_pencilSpectralSplit_exists
-- name    : OAI.Paper256.pencilSpectralSplit_exists
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T19:12:17.719238+00:00
-- url     : https://prove2.me/theorems/84bce6e1-9abf-46fc-84c0-8bff3668a3d5
-- title:
--   Splitting the eigenvalues of a nonzero singular positive semidefinite matrix into positive and nonpositive parts
-- statement:
--   Let $A$ be a real symmetric $m\times m$ matrix and let $\lambda_1,\dots,\lambda_m$ be its eigenvalues, listed with multiplicity in the order of a fixed orthonormal eigenbasis $u_1,\dots,u_m$ (so $Au_i=\lambda_iu_i$). Suppose that $A$ is positive semidefinite, $A\neq0$, and $A$ is not positive definite. Then there exist integers $a\ge1$ and $c\ge1$ and a bijection
--   $$\sigma:\{1,\dots,a\}\sqcup\{1,\dots,c\}\to\{1,\dots,m\}$$
--   such that $\lambda_{\sigma(i)}>0$ for every $i$ in the first part and $\lambda_{\sigma(j)}\le0$ for every $j$ in the second part.
--
--   Such a bijection, a *spectral split* of $A$, separates the eigenvectors of $A$ into those with positive eigenvalue and those in the kernel; since $A$ is positive semidefinite, the eigenvalues of the second group are in fact $0$, and $a+c=m$. Both groups are nonempty, which is what is needed to cut a spectrahedral representation into two genuine diagonal blocks.
--
--   **Formalization Note** The eigenvalues are Mathlib's `IsHermitian.eigenvalues` of the Hermitian matrix $A$ (indexed compatibly with `eigenvectorUnitary`). The conclusion is nonemptiness of the structure `PencilSpectralSplit A`, which records $0<a$, $0<c$, an equivalence `Fin a ⊕ Fin c ≃ Fin m` and the two sign conditions, the second stated as the negation of $0<\lambda$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/HyperbolicCones/SplitFrame.lean#L23-L46

import Mathlib
import Definitions.Def_HyperbolicCones
import Definitions.Def_OAI_Analysis_HyperbolicCones_Model
import Definitions.Def_OAI_Analysis_HyperbolicCones_MatrixBasic
import Definitions.Def_OAI_Analysis_HyperbolicCones_MatrixLinear
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilConjugation
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilBlocks
import Definitions.Def_OAI_Analysis_HyperbolicCones_RawBlocks
import Definitions.Def_OAI_Analysis_HyperbolicCones_KernelSpectrum
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilTopology
import Definitions.Def_OAI_Analysis_HyperbolicCones_SplitBasic
import Definitions.Def_OAI_Analysis_HyperbolicCones_SplitFrame

open OAI OAI.Paper256
open Set Matrix
open scoped Matrix.Norms.L2Operator
universe u

theorem OAI.Paper256.pencilSpectralSplit_exists {m : ℕ} (A : Sym m)
    (hA : (A : Mat m ℝ).PosSemidef) (hne : (A : Mat m ℝ) ≠ 0)
    (hnpd : ¬ (A : Mat m ℝ).PosDef) : Nonempty (PencilSpectralSplit A) := by sorry
