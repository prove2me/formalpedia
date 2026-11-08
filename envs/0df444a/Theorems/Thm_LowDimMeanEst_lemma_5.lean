-- Prove2me | Theorems.Thm_LowDimMeanEst_lemma_5
-- name    : LowDimMeanEst.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T04:53:29.575204+00:00
-- url     : https://prove2.me/theorems/0689a604-c60d-4e26-8c07-d0f0845304a3
-- title:
--   Lemma 5 — Algorithm 1 is shift-and-scale equivariant: $\hat\mu(aX+b,\delta)=a\hat\mu(X,\delta)+b$ for $a>0$
-- statement:
--   **Lemma 5.** Let the initial estimator $\kappa$ of Algorithm 1 be shift-and-scale equivariant: $\kappa(ay_1+b,\dots,ay_m+b)=a\,\kappa(y_1,\dots,y_m)+b$ for all $a>0$, $b\in\mathbb R^d$. Then for all samples $X=(x_1,\dots,x_{m+N})$, $\delta\in(0,1)$, $a>0$ and $b\in\mathbb R^d$, the outputs of Algorithm 1 on $aX+b$ are exactly the points
--
--   $$\hat\mu(aX+b,\delta)=a\,\hat\mu(X,\delta)+b,$$
--
--   where $\hat\mu(X,\delta)$ ranges over the outputs on $X$.
--
--   Shifting and scaling the data therefore moves the estimate in the same way, so the estimation error scales with the data.
--
--   **Formalization Note** Fact 49's estimator is shift-scale-and-rotation equivariant; only shift-and-scale equivariance is assumed. This is the only statement of the mission that assumes equivariance.
--
--   Differences from the source:
--   - generalization: Algorithm 1 with Fact 49's estimator (shift-scale-and-rotation equivariant) on √(n log(1/δ)) samples → any initial estimator that is shift-and-scale equivariant, on any number m of initial samples; reason: Fact 49's estimator has this property and the proof uses nothing else (p.51); m = √(n log(1/δ)) is a special case
--   - generalization: Algorithm 2 as printed → the corrected relation IsTrimOutput (correction C1 of Lemma 3); reason: on inputs where the printed search has an output the two have the same outputs, so the statement specializes to the source's
--   - encoding: µ̂(aX + b, δ) = aµ̂(X, δ) + b → the outputs on aX + b are exactly aµ̂ + b for the outputs µ̂ on X; reason: Algorithm 1 is a relation
-- source:
--   Lee, Mathashery, Valiant, Wang, Optimal Sub-Gaussian Mean Estimation in Low Dimensions, STOC 2027 submission (manuscript sha256 7316d30e…), Lemma 5, p.9 (restated p.51)

import Mathlib
import Definitions.Def_LowDimMeanEst_Algorithm1

namespace LowDimMeanEst

/-- **Lemma 5**, p.9 (restated p.51).

Lee, Mathashery, Valiant, Wang, *Optimal Sub-Gaussian Mean Estimation in Low Dimensions*, STOC 2027
submission (manuscript sha256 7316d30e…).

"Suppose X is a set of samples in ℝᵈ. Then for any δ ∈ (0, 1) and any scale a > 0 and shift vector
b ∈ ℝᵈ, the output of Algorithm 1 satisfies µ̂(aX + b, δ) = aµ̂(X, δ) + b."

**Formalization Note.**
* The initial estimator `kap` is assumed shift-and-scale equivariant,
  `kap(a y + b) = a kap(y) + b` for `a > 0`, which is the part of Fact 49's "Furthermore" clause the
  proof uses (p.51). This is the only item of the mission that assumes equivariance.
* Algorithm 1 is the relation `IsAlg1Output`: the outputs on `aX + b` are exactly `aµ̂ + b` for the
  outputs `µ̂` on `X`.
-/
theorem lemma_5 {d m N : ℕ} (kap : (Fin m → E d) → E d)
    (hkap : ∀ (a : ℝ) (b : E d) (y : Fin m → E d), 0 < a → kap (fun j => a • y j + b) = a • kap y + b)
    (δ a : ℝ) (b : E d) (hδ0 : 0 < δ) (hδ1 : δ < 1) (ha : 0 < a) (x : Fin (m + N) → E d)
    (mu0 : E d) :
    IsAlg1Output kap δ (fun i => a • x i + b) mu0 ↔
      ∃ muHat : E d, IsAlg1Output kap δ x muHat ∧ mu0 = a • muHat + b := by sorry

end LowDimMeanEst
