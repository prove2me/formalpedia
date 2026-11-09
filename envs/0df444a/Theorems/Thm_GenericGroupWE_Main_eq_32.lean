-- Prove2me | Theorems.Thm_GenericGroupWE_Main_eq_32
-- name    : GenericGroupWE.Main.eq_32
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:54:04.912983+00:00
-- url     : https://prove2.me/theorems/b1da14ec-56ce-4756-8ae7-b950cba4b4cd
-- title:
--   §6.4, eq. (32) — Equations transfer to the replacement coordinates
-- statement:
--   Fix the actual tested stack $A=\sum_b\lambda_bA(b)$, a sample $t$, and coefficients $\mu_{ij}$ expressing its surviving columns in the first $\delta$ geometric combinations, which form a basis, with $\delta\le R^2$ so that every form used is an available weight form. Define $s_i(b)=\sum_j\mu_{ij}\ell_{j,t}(b)$ and the actual evaluation functional $L(f)=\sum_b\lambda_b f(s_1(b),\ldots,s_N(b))$. Then
--
--   $$L((x_i^2-x_i)f)=L(q_sf)=0\qquad(\deg f+2\le r+2d).$$
--
--   The functional and replacement coordinates are computed from the fixed representation and basis choice; no annihilation property is assumed.
--
--   Differences from the source:
--   - generalization: the selected nonzero sample of a low-rank unsatisfiable prime-field instance → any field, any finite family of polynomials of total degree at most 2, any tested stack, and any sample with the stated geometric basis and coordinate expressions using delta<=R^2 available forms; reason: the transfer argument uses the tests and these available column relations alone; the source choices satisfy the bound by (29) and rho<R
--   - encoding: L is defined through degree r+2d → the same evaluation formula defines L on every polynomial; reason: only the displayed degree range is asserted
--   - encoding: finite indexed families and field residues → Fin-indexed families and ZMod prime fields; reason: zero-based indices and explicit finite carriers change no mathematical instance
-- source:
--   Hair and Sahai, Witness Encryption via Prime-Order Generic Groups, STOC 2027 submission #47 (PDF built 2026-11-02; SHA-256 0b7f14e2db9bb3e199883ab907f854b7b5884c7c9f3d1e4c306bb71e89b659cb), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/47.pdf, §6.4, eq. (32), PDF p. 28 (printed p. 27).

import Definitions.Def_GenericGroupWE_Main_Tables

namespace GenericGroupWE.Main
open scoped BigOperators

theorem eq_32 (K : Type*) [Field K] (N k d δ : ℕ) (hd : 1 ≤ d)
    (havailable : δ ≤ (rankTarget N d)^2)
    (q : Fin k → MvPolynomial (Fin N) K)
    (hq : ∀ s, (q s).totalDegree ≤ 2)
    (coefficients : BooleanAssignment N → K)
    (hmem : representedStack (d := d) coefficients ∈ testedSpace q)
    (t : Fin (N * ((rankTarget N d)^2 + weightDegree N) + 1))
    (μ : Fin N → Fin δ → K)
    (hbasis : IsReplacementBasis hd (representedStack (d := d) coefficients) t.val μ) :
    AnnihilatesEquations q (replacementFunctional coefficients t.val μ)
      (weightDegree N + 2*d) := by sorry

end GenericGroupWE.Main
