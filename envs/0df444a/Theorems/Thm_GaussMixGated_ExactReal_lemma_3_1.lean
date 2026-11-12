-- Prove2me | Theorems.Thm_GaussMixGated_ExactReal_lemma_3_1
-- name    : GaussMixGated.ExactReal.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T15:25:38.568556+00:00
-- url     : https://prove2.me/theorems/1046fd3a-de89-42eb-a244-12346a25a0f4
-- title:
--   Lemma 3.1 — Jet moments
-- statement:
--   Let $F:\mathbb R^n\to\mathbb R^r$ be a nonzero polynomial map of degree at most $q$, let $v>0$, $u\in\mathbb R^n$ and $G\sim N(0,I_n)$. With $J_F(x)=\sum_{h=0}^q\frac{v^h}{h!}\|D^hF(x)\|_F^2$ and $M(u)=\mathbb E\|F(u+\sqrt vG)\|^2$,
--
--   $$M(u)\le\mathbb EJ_F(u+\sqrt vG)\le2^qM(u),\qquad \mathbb EJ_F(u+\sqrt vG)^{-2}\le\frac{e^{12q}}{M(u)^2}.$$
--
--   Here $\|D^hF(x)\|_F$ is the entrywise (Frobenius) norm of the $h$-th derivative. The lemma supplies both the upper and the inverse-moment bound on which the gate of Lemma 3.2 rests.
--
--   **Formalization Note** The inverse second moment is a lower Lebesgue integral in $[0,\infty]$, so no integrability is presupposed.
--
--   Differences from the source:
--   - encoding: F supplied by a division-free arithmetic circuit → F given by its coordinate polynomials of total degree ≤ q; reason: the circuit clause concerns representation only; every polynomial map has such a circuit
--   - encoding: E J_F^{-2} → lower Lebesgue integral of ofReal(J_F^{-2}) compared in ℝ≥0∞; reason: J_F > 0 everywhere for nonzero F; no integrability side condition
-- source:
--   Zheng, Xie, He, Learning Finite Gaussian Location Mixtures via Gated Moments and Posterior Covers, STOC 2027 submission #36 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/36.pdf, PDF p. 9 (printed p. 7), §3.2, Lemma 3.1, (15)

import Mathlib
import Definitions.Def_GaussMixGated_ExactReal_Jet

open MeasureTheory

namespace GaussMixGated.ExactReal

/-- Lemma 3.1 (Jet moments) (Zheng–Xie–He, STOC 2027 #36, PDF p. 9): for a nonzero polynomial
map `F : ℝ^n → ℝ^r` of degree at most `q`, `v > 0` and `G ∼ N(0, I_n)`,
`M(u) ≤ E J_F(u + √v G) ≤ 2^q M(u)` and `E J_F(u + √v G)^{−2} ≤ e^{12q} / M(u)²`. -/
theorem lemma_3_1 {n r : ℕ} (F : PolyMap n r) (q : ℕ) (hF : F.DegLE q) (hF0 : F ≠ 0)
    (v : ℝ) (hv : 0 < v) (u : Fin n → ℝ) :
    momentM F v u ≤ ∫ g, jet F q v (u + Real.sqrt v • g) ∂gaussVec n ∧
    ∫ g, jet F q v (u + Real.sqrt v • g) ∂gaussVec n ≤ 2 ^ q * momentM F v u ∧
    ∫⁻ g, ENNReal.ofReal ((jet F q v (u + Real.sqrt v • g))⁻¹ ^ 2) ∂gaussVec n ≤
      ENNReal.ofReal (Real.exp (12 * q) / momentM F v u ^ 2) := by sorry

end GaussMixGated.ExactReal
