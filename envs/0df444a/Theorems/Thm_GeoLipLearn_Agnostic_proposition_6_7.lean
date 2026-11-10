-- Prove2me | Theorems.Thm_GeoLipLearn_Agnostic_proposition_6_7
-- name    : GeoLipLearn.Agnostic.proposition_6_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T18:52:45.318599+00:00
-- url     : https://prove2.me/theorems/57b4e6b7-7901-468b-a9d9-a6caf79d6c12
-- title:
--   Proposition 6.7 (Accuracy after smoothing)
-- statement:
--   Let $p$ be a polynomial, $c\in\mathbb R$ and $0<\varepsilon\le1/4$. Set $L=\varepsilon^{-1}$, $s=2\varepsilon^2$ and $q=C_L(U_s(p-c))$, using the same $s$ for the corrector probes. If $\|p-c\|_2<10$ and $\Gamma(p)\le e^{-4/\varepsilon^4}$, then
--   $$\|R[q]-(p-c)\|_1\le30\varepsilon.$$
--   This quantifies the combined smoothing, clipping and ideal correction error.
--
--   Differences from the source:
--   - encoding: Euclidean space, Gaussian norms, and the norm of the scalar gradient → EuclideanSpace ℝ (Fin d), stdGaussian, extended nonnegative eLpNorm, and the operator norm of fderiv; reason: the scalar derivative has the same norm as the Euclidean gradient; extended norms retain infinity rather than returning a junk zero
--   - generalization: Section 6.1 chooses c=E p; Proposition 6.7 assumes ∥p−c∥₂<10 → c is any real satisfying the displayed norm bound; reason: the proposition and Section 6.4 use only this bound, never c = E p; the section's centre c = E p satisfies ∥p−c∥₂ ≤ 2 < 10 (§6.1), so every source instance is covered
-- source:
--   Lange, Marcussen and Vasilyan, Geometrically Constrained Learning II: Agnostic Proper Learning of Lipschitz Functions, STOC 2027 submission (manuscript sha256 45cb3c98836346299afa2ee9b2ff10d9d9a3fc8dcbbb9ecc23da2c89a9de615d), p. 23, Proposition 6.7

import Definitions.Def_GeoLipLearn_Agnostic_Corrector

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace GeoLipLearn.Agnostic

theorem proposition_6_7 (d : ℕ) (p : Poly d) (c ε : ℝ) (hε : 0 < ε ∧ ε ≤ 1/4)
    (hp : normG 2 (fun x => evalPoly p x-c) < 10)
    (hΓ : defect (evalPoly p) ≤ Real.exp (-4/ε^4)) :
    let q := fun x => clip ε⁻¹ (ou (2*ε^2) (fun y => evalPoly p y-c) x)
    normG 1 (fun x => corrector ε⁻¹ (2*ε^2) q x - (evalPoly p x-c)) ≤
      ENNReal.ofReal (30*ε) := by sorry

end GeoLipLearn.Agnostic
