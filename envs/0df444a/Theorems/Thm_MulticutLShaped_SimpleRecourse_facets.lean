-- Prove2me | Theorems.Thm_MulticutLShaped_SimpleRecourse_facets
-- name    : MulticutLShaped.SimpleRecourse.facets
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T09:03:31.831791+00:00
-- url     : https://prove2.me/theorems/06d6f144-686d-4eeb-ab61-b56995cc8472
-- title:
--   Section 5, p. 389 — $\Psi_i$ has $J+1$ facets and $\Psi$ at most $(J+1)^{m_2}$
-- statement:
--   In the simple recourse problem (3), (19)–(20) with $J$ realizations per row and $q_{ij}\ge0$, there are real numbers $a_{il},d_{il}$ ($i=1,\dots,m_2$, $l=1,\dots,J+1$) such that:
--
--   1. for each $i$, the expected recourse function of row $i$ is the maximum of $J+1$ affine functions,
--   $$
--   \Psi_i(\chi_i)=\max_{1\le l\le J+1}\big(a_{il}\chi_i+d_{il}\big)\qquad\text{for all }\chi_i\in\mathbb R;
--   $$
--   2. consequently, by separability,
--   $$
--   \Psi(\chi)=\max_{\sigma}\ \sum_{i=1}^{m_2}\big(a_{i\sigma(i)}\chi_i+d_{i\sigma(i)}\big)\qquad\text{for all }\chi\in\mathbb R^{m_2},
--   $$
--   the maximum ranging over the $(J+1)^{m_2}$ maps $\sigma:\{1,\dots,m_2\}\to\{1,\dots,J+1\}$.
--
--   The paper uses this count to compare the multicut bound $Jm_2+1$ with the worst-case number of iterations of the L-shaped method, which is the number of facets of $\Psi$.
--
--   **Formalization Note.** The paper says $\Psi_i$ "contains $J+1$ facets"; coinciding $h_{ij}$ or vanishing $p_{ij}q_{ij}$ give fewer distinct pieces, so we state "at most $J+1$" by allowing repeated affine functions in the list. The bound on $\Psi$ is stated as a maximum over the $(J+1)^{m_2}$ choices of one piece per row.
-- source:
--   Birge and Louveaux, A multicut algorithm for two-stage stochastic linear programs, Eur. J. Oper. Res. 34 (1988), p. 389, Section 5

import Mathlib
import Definitions.Def_MulticutLShaped_SimpleRecourse_Model

namespace MulticutLShaped.SimpleRecourse

variable {n1 m1 m2 J : ℕ}

/-- p. 389: each `Ψ_i` is the maximum of (at most) `J + 1` affine functions of `χ_i` (its facets),
and, `Ψ` being separable in `i`, `Ψ` is the maximum of (at most) `(J + 1)^{m2}` affine functions of
`χ`, indexed by the choices `σ : Fin m2 → Fin (J + 1)` of one facet per row. -/
theorem facets (inst : Instance n1 m1 m2 J) :
    ∃ a d : Fin m2 → Fin (J + 1) → ℝ,
      (∀ i (χi : ℝ), PsiI inst i χi =
        ((Finset.univ.sup' Finset.univ_nonempty fun l => a i l * χi + d i l : ℝ) : EReal)) ∧
      ∀ χ : Fin m2 → ℝ, Psi inst χ =
        ((Finset.univ.sup' Finset.univ_nonempty
          fun σ : Fin m2 → Fin (J + 1) => ∑ i, (a i (σ i) * χ i + d i (σ i)) : ℝ) : EReal) := by sorry

end MulticutLShaped.SimpleRecourse
