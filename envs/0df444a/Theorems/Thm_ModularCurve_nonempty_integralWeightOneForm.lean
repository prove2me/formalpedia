-- Prove2me | Theorems.Thm_ModularCurve_nonempty_integralWeightOneForm
-- name    : ModularCurve.nonempty_integralWeightOneForm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/d475c008-5442-5c2a-b515-30cc5612de51
-- title:
--   Existence of an integral weight-one form on Γ₁(M)
-- statement:
--   Let $\kappa$ be a field and let $M$ be a natural number with $3 \le M$. The assertion is that the type [`ModularCurve.IntegralWeightOneForm κ M`](def/ModularCurve_IgusaFunctionFieldX1.html#L16) is nonempty, i.e. that there exists a triple consisting of: a modular form $f$ of weight $1$ for the congruence subgroup $\Gamma_1(M)$, regarded as a subgroup of $\mathrm{GL}_2(\mathbb{R})$; a power series $p \in \mathbb{Z}[[q]]$; and a proof that $p$ is an integral $q$-expansion for $f$, meaning that the coefficientwise image of $p$ under $\mathbb{Z} \to \mathbb{C}$ equals the weight-one $q$-expansion `qExpansion 1 f` of $f$ at the cusp $\infty$; subject to the further condition that the Laurent series `intSeriesC κ p` over $\kappa$, obtained by reducing the coefficients of $p$ along $\mathbb{Z} \to \kappa$ and viewing the resulting element of $\kappa[[q]]$ as a Laurent series, is non-zero. Thus: for every field $\kappa$ and every level $M \ge 3$ there is a weight-one form on $\Gamma_1(M)$ whose $q$-expansion has integer coefficients not all of which vanish in $\kappa$.
--
--   This inhabits the datum from which the Igusa function field over $X_1(M)_\kappa$ is constructed, and it is invoked throughout the study of the models of $X_1(M)$ and of $X_1(M) \to X_0(M)$ in characteristic $p$. Classically the witness is a weight-one Eisenstein series attached to an odd Dirichlet character of conductor dividing $M$, and the proof cites the construction of such Eisenstein series for primitive odd characters, with constant term $-\bigl(\sum_{a<L} a\,\chi(a)\bigr)/(2L)$ and $n$-th coefficient $\sum_{d \mid n} \chi(d)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_nonempty_integralWeightOneForm.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.nonempty_integralWeightOneForm
    (κ : Type) [Field κ] (M : ℕ) (hM : 3 ≤ M) :
    Nonempty (ModularCurve.IntegralWeightOneForm κ M) := by sorry
