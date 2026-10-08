-- Prove2me | Theorems.Thm_IRLSM_Convergence_proposition_6_1
-- name    : IRLSM.Convergence.proposition_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:52:34.326929+00:00
-- url     : https://prove2.me/theorems/c74a9926-fa3d-423b-a3d2-b29d4fb9756c
-- title:
--   Proposition 6.1 — monotonicity of $\mathcal J$ along IRLS-M, $\mathcal J\ge\|X^\ell\|_*$, and $\|X^{\ell+1}-X^\ell\|_F\to0$
-- statement:
--   Let $(X^\ell,\varepsilon_\ell)$ be a run of the IRLS-M algorithm with any $K$ and any $\gamma>0$, and let $W^\ell$ be its weights. Then:
--
--   1. $\mathcal J(X^{\ell+1},W^{\ell+1})\le\mathcal J(X^\ell,W^\ell)$;
--   2. $\mathcal J(X^\ell,W^\ell)\ge\|X^\ell\|_*$;
--   3. there is a constant $\mathscr A>0$ such that
--   $$2\mathscr A\big[\mathcal J(X^\ell,W^\ell)-\mathcal J(X^{\ell+1},W^{\ell+1})\big]\ge\|X^{\ell+1}-X^\ell\|_F^2,$$
--   and consequently
--   $$\lim_{\ell\to\infty}\|X^{\ell+1}-X^\ell\|_F^2=0.$$
--
--   These basic properties of the iterates hold without any assumption on $\mathcal S$ and are the starting point of the convergence analysis.
--
--   **Formalization Note** Matrices are real ($n\times p$, with the paper's standing assumption $n\le p$ where $n\times n$ objects occur); the measurement map is $\mathcal S(X)_l=\langle A_l,X\rangle$ for measurement matrices $A_1,\dots,A_m$, so $\mathcal S^*$ is $u\mapsto\sum_l u_lA_l$ and $\langle\cdot,\cdot\rangle$ is the trace inner product. Items 1–3 are stated for $\ell\ge1$ and for indices before the algorithm stops ($\varepsilon_\ell>0$, resp. $\varepsilon_{\ell+1}>0$): the algorithm never defines $X^0$, and at the stop the weight formula divides by $\varepsilon_\ell=0$. After the stop the iterates are frozen, so the limit is stated for the whole sequence. The constant $\mathscr A$ may depend on the run, as in the page's proof. No surjectivity of $\mathcal S$ is assumed.
-- source:
--   Fornasier, Rauhut, Ward, Low-rank matrix recovery via iteratively reweighted least squares minimization, arXiv:1010.2471v4 (2011), Proposition 6.1, (6.1)–(6.2), p. 15 (proof pp. 15–16)

import Mathlib
import Definitions.Def_IRLSM_Convergence_Algorithm

open HighDimStat.MatrixRank Matrix Filter Topology

namespace IRLSM.Convergence

/-- **Proposition 6.1.** Let `(X^ℓ, W^ℓ, ε_ℓ)` be the output of the IRLS-M algorithm (any `K`,
any `γ > 0`). Then
(i) `𝒥(X^{ℓ+1}, W^{ℓ+1}) ≤ 𝒥(X^ℓ, W^ℓ)`;
(ii) `𝒥(X^ℓ, W^ℓ) ≥ ‖X^ℓ‖_*`;
(iii) there is a constant `𝒜 > 0` with `2𝒜 [𝒥(X^ℓ, W^ℓ) − 𝒥(X^{ℓ+1}, W^{ℓ+1})] ≥ ‖X^{ℓ+1} − X^ℓ‖²_F`
(6.1); in particular `‖X^{ℓ+1} − X^ℓ‖²_F → 0` (6.2).

Fornasier–Rauhut–Ward, arXiv:1010.2471v4, Proposition 6.1, p. 15 (proof pp. 15–16).

Formalization Notes: real matrices; `W^ℓ` is `Wseq X ε ℓ`. (i)–(iii) are stated for `ℓ ≥ 1`
and for indices before the stop (`ε_ℓ > 0`, resp. `ε_{ℓ+1} > 0`): the algorithm never defines
`X⁰`, and at the stop `W^ℓ` is undefined on the page (its formula divides by `ε_ℓ = 0`). After the
stop all iterates are frozen, so (6.2) is stated for the whole sequence. The page's `𝒜` depends on
the run, as here (`∃ C` after the run is fixed). `n ≤ p` is the page's standing assumption
(p. 4); no surjectivity of `S` is assumed (a run already provides feasible iterates). -/
theorem proposition_6_1 {n p m : ℕ} (A : Fin m → Matrix (Fin n) (Fin p) ℝ) (M : Fin m → ℝ)
    (K : ℕ) (γ : ℝ) (X : ℕ → Matrix (Fin n) (Fin p) ℝ) (ε : ℕ → ℝ) (hnp : n ≤ p) (hγ : 0 < γ)
    (hrun : IsRun A M K γ X ε) :
    (∀ ℓ : ℕ, 1 ≤ ℓ → 0 < ε (ℓ + 1) →
      J (X (ℓ + 1)) (Wseq X ε (ℓ + 1)) ≤ J (X ℓ) (Wseq X ε ℓ)) ∧
    (∀ ℓ : ℕ, 1 ≤ ℓ → 0 < ε ℓ → nuclearNorm (X ℓ) ≤ J (X ℓ) (Wseq X ε ℓ)) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ ℓ : ℕ, 1 ≤ ℓ → 0 < ε (ℓ + 1) →
      frobeniusNorm (X (ℓ + 1) - X ℓ) ^ 2 ≤
        2 * C * (J (X ℓ) (Wseq X ε ℓ) - J (X (ℓ + 1)) (Wseq X ε (ℓ + 1)))) ∧
    Tendsto (fun ℓ : ℕ => frobeniusNorm (X (ℓ + 1) - X ℓ) ^ 2) atTop (𝓝 0) := by sorry

end IRLSM.Convergence
