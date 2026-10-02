-- Prove2me | Theorems.Thm_LeblSCV_Germs_germRing_isNoetherianRing
-- name    : LeblSCV.Germs.germRing_isNoetherianRing
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T10:10:31.673435+00:00
-- url     : https://prove2.me/theorems/31034e4d-82b7-410f-96d4-4be46a13fc6f
-- title:
--   Theorem 6.4.1 — $\mathcal{O}_p$ is Noetherian
-- statement:
--   For every $n$ and every $p \in \mathbb{C}^n$, the ring $\mathcal{O}_p$ of germs at $p$ of holomorphic functions is **Noetherian**: every ideal $I \subset \mathcal{O}_p$ is finitely generated, i.e. there are $f_1, \dots, f_k \in I$ such that every $g \in I$ can be written as
--   $$ g = c_1 f_1 + \cdots + c_k f_k, \qquad c_1, \dots, c_k \in \mathcal{O}_p. $$
--
--   For $n = 1$ the ring is even a principal ideal domain; for $n > 1$ it is not, but it is still Noetherian. This is what makes the local theory of analytic varieties finite: every germ of a variety is cut out by finitely many holomorphic functions.
--
--   **Formalization Note.** `GermRing n p` is the subring of Mathlib's germ ring `(𝓝 p).Germ ℂ` of germs with a representative complex-differentiable near $p$ (Definition 6.1.2); `IsNoetherianRing` is Mathlib's class. Convergence matters: the ring of formal power series is also Noetherian, but it is a different ring and not the subject of this theorem.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 181, Theorem 6.4.1

import Mathlib
import Definitions.Def_LeblSCV_Germs_holomorphicGerms

namespace LeblSCV.Germs

/-- Theorem 6.4.1 (Lebl, p. 181). For every `n` and every `p ∈ ℂⁿ`, the ring `𝒪_p` of germs at
`p` of holomorphic functions is Noetherian: every ideal is finitely generated. -/
theorem germRing_isNoetherianRing (n : ℕ) (p : Fin n → ℂ) : IsNoetherianRing (GermRing n p) := by sorry

end LeblSCV.Germs
