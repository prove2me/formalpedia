-- Prove2me | Theorems.Thm_ModularCurve_qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit
-- name    : ModularCurve.qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/088c8d45-fb84-58cb-a56c-0cfe518effa7
-- title:
--   q-expansion of Δ as integral series qprod(1-qⁿ)²⁴
-- statement:
--   The statement is a closed identity in `PowerSeries ℂ`, with no variables or hypotheses. On the left stands `UpperHalfPlane.qExpansion 1 ModularForm.discriminant`, Mathlib's $q$-expansion of period $1$ at the cusp $i\infty$ of the modular discriminant $\Delta$, i.e. the power series whose $n$-th coefficient is the $n$-th Taylor coefficient at $q=0$ of the function of $q$ induced by $\Delta$. On the right stands the coefficientwise image under the ring homomorphism $\mathbb{Z}\to\mathbb{C}$ of the integral series $X \cdot$ [`ModularCurve.dedekindEtaUnit`](def/ModularCurve_X0.html#L127), where [`ModularCurve.dedekindEtaUnit`](def/ModularCurve_X0.html#L127) is defined as the twenty-fourth power of [`ModularCurve.etaProd`](def/ModularCurve_X0.html#L119), itself the infinite product $\prod'_{n\,:\,\mathbb{N}} (1 - X^{n+1})$ in `PowerSeries ℤ` taken in the product (coefficientwise) topology. Thus the analytic $q$-expansion of $\Delta$ equals $q\prod_{n\ge 1}(1-q^n)^{24}$ with all coefficients obtained by casting integers into $\mathbb{C}$; in particular every coefficient of the $q$-expansion of $\Delta$ lies in the image of $\mathbb{Z}$.
--
--   This is the classical product formula $\Delta = q\prod_{n\ge1}(1-q^n)^{24}$, in the form identifying the analytic $q$-expansion with the integral formal series used elsewhere in the development, so that integrality of the Ramanujan coefficients $\tau(n)$ and the normalisation $\tau(1)=1$ are available. It is used by the work on modular units and on $q$-expansions of forms on $X_0(N)$, including the level-one auxiliary results and congruences for coefficients of cusp forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit.lean

import Definitions.Def_ModularCurve_X0
import Mathlib.NumberTheory.ModularForms.Discriminant

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit : UpperHalfPlane.qExpansion 1 ModularForm.discriminant = PowerSeries.map (Int.castRingHom ℂ) (PowerSeries.X * ModularCurve.dedekindEtaUnit) := by sorry
