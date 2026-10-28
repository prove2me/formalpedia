-- Prove2me | Theorems.Thm_NonAbelianDMNRG_Recursion_eq_39_41_42
-- name    : NonAbelianDMNRG.Recursion.eq_39_41_42
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T09:29:03.819675+00:00
-- url     : https://prove2.me/theorems/4600bac8-e966-4b1c-95b4-c0ad898b9c22
-- title:
--   Eqs. (39), (41)–(42) — invariance of $R^{[n]}$ passes to $\mathrm{Tr}_{\mathrm{site}}R^{[n]}$ and to $R^{[n-1]}$
-- statement:
--   Let $G$ be a group whose labels $Q$ carry unitary representations $\pi_Q$. Let $K$ (kept multiplets $u$, labels $Q_u$), $\Lambda$ (local multiplets $\mu$ of site $n$, labels $q_\mu$) and $D$ (discarded multiplets $d$, labels $Q_d$) be finite, and let $w_d$ be real weights. Let $R$ be an operator on the new space (block states $\otimes$ local states) that is scalar under the symmetry,
--   $$
--   U(g)\, R\, U(g)^\dagger = R \quad\text{for all } g\in G,\qquad U(g) = V(g)\otimes L(g).
--   $$
--   Then:
--   1. (41) the partial trace over the site is invariant under the block symmetry: $V(g)\,\operatorname{Tr}_{\mathrm{site}}\{R\}\,V(g)^\dagger = \operatorname{Tr}_{\mathrm{site}}\{R\}$ for all $g$;
--   2. (42) the operator of iteration $n-1$ given by (39),
--   $$
--   R^{[n-1]} = \sum_{d\in D} w_d \sum_{Q^z} |d, Q_d, Q^z\rangle\langle d, Q_d, Q^z| \;+\; \operatorname{Tr}_{\mathrm{site}}\{R\},
--   $$
--   on the space whose multiplets are the discarded ones followed by the kept ones, satisfies $U(g)\,R^{[n-1]}\,U(g)^\dagger = R^{[n-1]}$ for all $g$, where $U(g)$ now acts block-diagonally on discarded and kept multiplets.
--
--   This is the induction step showing that every truncated reduced density matrix of the DM-NRG recursion is scalar under the symmetry.
--
--   **Formalization Note** In the paper the weights are the Boltzmann factors $e^{-\beta E_i^{n-1}} d^{N-n+1}/\mathcal Z$; the statement holds for arbitrary real weights. No positivity or trace normalization of $R$ is needed.
-- source:
--   Tóth, Moca, Legeza, Zaránd, Density matrix numerical renormalization group for non-Abelian symmetries, arXiv:0802.4332v1, p. 7, eqs. (39), (41), (42)

import Mathlib
import Definitions.Def_WildeQIT_partialTrace
import Definitions.Def_NonAbelianDMNRG_Recursion_Multiplets
open Matrix
open scoped Kronecker

namespace NonAbelianDMNRG.Recursion

/-- **Eqs. (39), (41)–(42), p. 7.** If `R` on the new space (block × site) is invariant under
`U(g) = V(g) ⊗ L(g)` for every `g`, then (41) its partial trace over the site is invariant under
`V(g)` for every `g`, and (42) the operator `R^{[n−1]}` of (39), the weighted discarded-state
projection plus `Tr_site R` on the kept states, is invariant under the symmetry transformation of
iteration `n − 1`. -/
theorem eq_39_41_42 {G : Type} [Group G] {Lab : Type} (dim : Lab → ℕ)
    (π : (Q : Lab) → G →* Matrix.unitaryGroup (Fin (dim Q)) ℂ)
    {K Λ D : Type} [Fintype K] [DecidableEq K] [Fintype Λ] [DecidableEq Λ]
    [Fintype D] [DecidableEq D]
    (Qu : K → Lab) (ql : Λ → Lab) (Qd : D → Lab) (w : D → ℝ)
    (R : Matrix (Multiplets dim Qu × Multiplets dim ql) (Multiplets dim Qu × Multiplets dim ql) ℂ)
    (hR : ∀ g : G, newRep dim π Qu ql g * R * (newRep dim π Qu ql g)ᴴ = R) :
    (∀ g : G, multipletRep dim π Qu g * WildeQIT.partialTraceRight R *
        (multipletRep dim π Qu g)ᴴ = WildeQIT.partialTraceRight R) ∧
    (∀ g : G, prevRep dim π Qd Qu g *
        truncatedOperator dim Qd Qu w (WildeQIT.partialTraceRight R) * (prevRep dim π Qd Qu g)ᴴ =
        truncatedOperator dim Qd Qu w (WildeQIT.partialTraceRight R)) := by sorry

end NonAbelianDMNRG.Recursion
