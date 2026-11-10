-- Prove2me | Theorems.Thm_GeoLipLearn_Agnostic_lemma_5_1
-- name    : GeoLipLearn.Agnostic.lemma_5_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T18:52:43.412869+00:00
-- url     : https://prove2.me/theorems/f201278f-9ca1-4d0b-ade1-3fc752063ac3
-- title:
--   Lemma 5.1 (Agreement with a bounded Lipschitz witness)
-- statement:
--   Let $p$ be a polynomial, $s>0$ and $B>0$. Put $q=C_B(U_sp)$ and $h(x)=\inf_y\{q(y)+\|x-y\|\}$. Then $h$ is globally 1-Lipschitz and takes values in $[-B,B]$, and
--   $$\Pr_{x\sim\gamma_d}[q(x)\ne h(x)]\le\Gamma(p)C_{s,B},\qquad C_{s,B}=(e^s-1)^{-2}e^{4B^2/(e^{2s}-1)}.$$
--   Moreover $\|q-h\|_1\le\|q-h\|_2\le2B\sqrt{\Gamma(p)C_{s,B}}$. This gives the bounded Lipschitz witness and its agreement and distance bounds.
--
--   Differences from the source:
--   - encoding: Euclidean space, Gaussian norms, and the norm of the scalar gradient → EuclideanSpace ℝ (Fin d), stdGaussian, extended nonnegative eLpNorm, and the operator norm of fderiv; reason: the scalar derivative has the same norm as the Euclidean gradient; extended norms retain infinity rather than returning a junk zero
--   - generalization: the bounded-label setup has B≥1 → the analytic conclusion is stated for every B>0; reason: this includes every source instance; the agreement argument uses only a positive clipping height
-- source:
--   Lange, Marcussen and Vasilyan, Geometrically Constrained Learning II: Agnostic Proper Learning of Lipschitz Functions, STOC 2027 submission (manuscript sha256 45cb3c98836346299afa2ee9b2ff10d9d9a3fc8dcbbb9ecc23da2c89a9de615d), p. 17, Lemma 5.1

import Definitions.Def_GeoLipLearn_Agnostic_Corrector

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace GeoLipLearn.Agnostic

theorem lemma_5_1 (d : ℕ) (p : Poly d) (s B : ℝ) (hs : 0 < s) (hB : 0 < B) :
    let q := fun x => clip B (ou s (evalPoly p) x)
    let h := mcShane q
    (LipschitzWith 1 h ∧ InRange B h) ∧
    (gaussian d).real {x | q x ≠ h x} ≤ defect (evalPoly p)*witnessConstant s B ∧
    normG 1 (q-h) ≤ normG 2 (q-h) ∧
    normG 2 (q-h) ≤ ENNReal.ofReal (2*B*Real.sqrt (defect (evalPoly p)*witnessConstant s B)) := by sorry

end GeoLipLearn.Agnostic
