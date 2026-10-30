-- Prove2me | Theorems.Thm_KingDiagonal_nonzero_spectrum
-- name    : KingDiagonal.nonzero_spectrum
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T03:14:19.524816+00:00
-- url     : https://prove2.me/theorems/d5cb05cd-e76f-4df8-813b-68737a53c0b7
-- title:
--   $X^*X$ and $XX^*$ share the same nonzero spectrum
-- statement:
--   Let $X$ be any complex $a\times b$ matrix. Then $X^*X$ and $XX^*$ have the same nonzero eigenvalues, counted with multiplicity. Equivalently, for every function $f:\mathbb R\to\mathbb R$ with $f(0) = 0$,
--
--   $$
--   \operatorname{Tr} f(X^*X) = \operatorname{Tr} f(XX^*).
--   $$
--
--   King applies this with $X = V_i$ and $f(x) = x^p$ to replace $\operatorname{Tr}(V_i^*V_i)^p$ by $\operatorname{Tr}(V_iV_i^*)^p = \|V_iV_i^*\|_p^p$, which (18) bounds.
--
--   **Formalization Note** $f(X^*X)$ is the continuous functional calculus of the positive semidefinite matrix $X^*X$.
--
--   Differences from the source:
--   - encoding: V_i*V_i and V_iV_i* share the same nonzero spectrum → Tr f(XᴴX) = Tr f(XXᴴ) for every f : ℝ → ℝ with f 0 = 0; reason: for two PSD matrices this family of trace identities holds exactly when their multisets of nonzero eigenvalues agree
--   - generalization: the block rows V_i of (16) → an arbitrary rectangular matrix X; reason: the spectral fact holds for every matrix; X = V_i is the page's instance
-- source:
--   King, An application of a matrix inequality in quantum information theory, arXiv:quant-ph/0412046v1, Sec. 4, first sentence, p.7

import Mathlib

open scoped Matrix

namespace KingDiagonal

/-- King, arXiv:quant-ph/0412046v1, Sec. 4, first sentence, p.7: the matrices `X*X` and `XX*` share
the same nonzero spectrum (with multiplicity), for every rectangular matrix `X` (the paper applies
this to `X = V_i`, to get `Tr (V_i*V_i)^p = Tr (V_iV_i*)^p`).

**Formalization Note.** "Same nonzero spectrum with multiplicity" is encoded as: for every function
`f : ℝ → ℝ` with `f 0 = 0`, `Tr f(X*X) = Tr f(XX*)` (`cfc f`). Since both matrices are positive
semidefinite, this family of trace identities holds exactly when the multisets of nonzero
eigenvalues coincide; zero eigenvalues contribute `f 0 = 0`. -/
theorem nonzero_spectrum {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (X : Matrix a b ℂ) (f : ℝ → ℝ) (hf : f 0 = 0) :
    (cfc f (Xᴴ * X)).trace = (cfc f (X * Xᴴ)).trace := by sorry

end KingDiagonal
