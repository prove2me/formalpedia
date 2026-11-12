-- Prove2me | Theorems.Thm_MatroidEquitability_proof_theorem_2_eq_5
-- name    : MatroidEquitability.proof_theorem_2_eq_5
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T06:32:41.862229+00:00
-- url     : https://prove2.me/theorems/cc182bec-1804-49ed-b563-9c83bb96af2d
-- title:
--   Proof of Theorem 2, the linear program and (5) — optimal solutions and complementary slackness
-- statement:
--   Let $E$ be a finite set and let $\mathcal F^+,\mathcal F^-$ be nonempty finite families of subsets of $E$. The linear program
--
--   $$
--   \max\ \gamma\quad\text{s.t.}\quad u(B)-u(D)\ge\gamma\ \ \forall B\in\mathcal F^+,\,D\in\mathcal F^-,\qquad 0\le u_e\le 1\ \ \forall e\in E
--   $$
--
--   and its dual have optimal solutions. For every optimal $(u,\gamma)$ and every optimal $(\lambda,x)$, writing $y:=\sum_{B,D}\lambda_{B,D}(\mathbf 1_B-\mathbf 1_D)$:
--
--   1. $\gamma=b-d$, where $b:=\min_{B\in\mathcal F^+}u(B)$ and $d:=\max_{D\in\mathcal F^-}u(D)$;
--   2. $x_e=\max\{0,y_e\}$ for every $e\in E$;
--   3. $u(B)-u(D)=\gamma$ whenever $\lambda_{B,D}>0$;
--   4. for every $e\in E$,
--
--   $$
--   y_e\le 0\ \text{ if }u_e=0,\qquad y_e=0\ \text{ if }0<u_e<1,\qquad y_e\ge 0\ \text{ if }u_e=1. \tag{5}
--   $$
--
--   These are the facts of linear programming duality on which the argument for Theorem 2 rests.
--
--   Differences from the source:
--   - generalization: $\mathcal F^+\sqcup\mathcal F^-$ the family of blocks of a block matroid with (4), so that $\gamma>1$ → arbitrary nonempty finite families of subsets of a finite set `E`, no matroid and no assumption on $\gamma$; reason: linear programming duality uses nothing else, and the page's families are an instance
--   - generalization: "Let $(u,\gamma)$ be an optimal primal solution", "Let $(\lambda,x)$ be an optimal dual solution", which presuppose existence → a conclusion asserting that both optimal solutions exist, then the page's claims for all optimal pairs; reason: this adds to the page's claims and removes none
--   - encoding: families of subsets, $u\in\mathbb R^E$, $\lambda$ on $\mathcal F^+\times\mathcal F^-$ → `Finset (Set α)`, `u : α → ℝ`, `lam : Set α → Set α → ℝ`, constrained only on `E` and on `Fp × Fm`; reason: Lean convention; the same instances
-- source:
--   Bérczi, Liu, Reis, Tarnawski, Weighted Equitability and Matroid-Constrained Discrepancy, arXiv:2608.13983 (held version sha256 0675891a…), Proof of Theorem 2, the linear program and (5), pp.8–9 (PDF pp.10–11)

import Mathlib
import Definitions.Def_MatroidEquitability_setWeight
import Definitions.Def_MatroidEquitability_IsPrimalOptimal
import Definitions.Def_MatroidEquitability_dualVector
import Definitions.Def_MatroidEquitability_IsDualOptimal

namespace MatroidEquitability

/-- The linear program of the proof of Theorem 2 and (5): both the program and its dual have optimal
solutions, and for every optimal pair `(u, γ)`, `(λ, x)` one has `γ = b − d` with
`b = min_{F⁺} u(B)`, `d = max_{F⁻} u(D)`; `x_e = max{0, y_e}`; `u(B) − u(D) = γ` whenever
`λ_{B,D} > 0`; and the sign conditions (5) on `y` (printed pp.8–9 = PDF pp.10–11 of
Bérczi, Liu, Reis, Tarnawski, *Weighted Equitability and Matroid-Constrained Discrepancy*, arXiv:2608.13983 (held version sha256 0675891a…)).

**Formalization Note.** No matroid and no assumption `γ > 1` are involved: `F⁺` and `F⁻` are arbitrary
nonempty finite families of subsets of the finite set `E`. -/
theorem proof_theorem_2_eq_5 {α : Type*} (E : Set α) (hE : E.Finite) (Fp Fm : Finset (Set α))
    (hFp : Fp.Nonempty) (hFm : Fm.Nonempty) (hFpE : ∀ B ∈ Fp, B ⊆ E) (hFmE : ∀ D ∈ Fm, D ⊆ E) :
    (∃ u γ, IsPrimalOptimal E Fp Fm u γ) ∧ (∃ lam x, IsDualOptimal E Fp Fm lam x) ∧
      ∀ u γ lam x, IsPrimalOptimal E Fp Fm u γ → IsDualOptimal E Fp Fm lam x →
        γ = Fp.inf' hFp (setWeight u) - Fm.sup' hFm (setWeight u) ∧
        (∀ e ∈ E, x e = max 0 (dualVector Fp Fm lam e)) ∧
        (∀ B ∈ Fp, ∀ D ∈ Fm, 0 < lam B D → setWeight u B - setWeight u D = γ) ∧
        ∀ e ∈ E,
          (u e = 0 → dualVector Fp Fm lam e ≤ 0) ∧
          (0 < u e → u e < 1 → dualVector Fp Fm lam e = 0) ∧
          (u e = 1 → 0 ≤ dualVector Fp Fm lam e) := by sorry

end MatroidEquitability
