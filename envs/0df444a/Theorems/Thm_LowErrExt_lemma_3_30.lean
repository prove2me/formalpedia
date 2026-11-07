-- Prove2me | Theorems.Thm_LowErrExt_lemma_3_30
-- name    : LowErrExt.lemma_3_30
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:54:31.791057+00:00
-- url     : https://prove2.me/theorems/718f195f-2213-4cd3-b43e-524ad9f698b2
-- title:
--   Lemma 3.30 — XOR lemma for $\varepsilon$-biased affine sources (corrected: $\varepsilon<1$)
-- statement:
--   Let $0\le\varepsilon<1$ and let $\mathbf X$ be an $\varepsilon$-biased affine source on $\mathbb F_2^n$. Then there is an affine source $\mathbf Z$ on $\mathbb F_2^n$ with
--   $$\mathrm{SD}(\mathbf X,\mathbf Z)\le 2^{n/2}\varepsilon$$
--   such that for every $y\in\mathbb F_2^n$:
--
--   1. if $\mathrm{bias}[\mathrm{IP}(\mathbf X,y)]=1$ then $\mathrm{bias}[\mathrm{IP}(\mathbf Z,y)]=1$;
--   2. if $\mathrm{bias}[\mathrm{IP}(\mathbf X,y)]\le\varepsilon$ then $\mathrm{bias}[\mathrm{IP}(\mathbf Z,y)]=0$.
--
--   An $\varepsilon$-biased affine source is close to the uniform distribution on its affine span.
--
--   Differences from the source:
--   - correction: no bound on ε → ε < 1; reason: counterexample: any X, ε = 1, y = 0. Every source is 1-biased affine and bias[IP(X, 0)] = 1 ≤ ε, so clause 2 demands bias[IP(Z, 0)] = 0, but IP(Z, 0) is constant and has bias 1 (proved in the sanity file)
--   - correction: no lower bound on ε → 0 ≤ ε; reason: counterexample: X the point mass at 0 and any ε < 0. Every bias of X is 1, so X is ε-biased affine, but SD(X, Z) ≥ 0 > 2^{n/2}ε for every Z
-- source:
--   D. Doron, J. Goodman, Low-Error Extractors, STOC 2027 submission (manuscript sha256 43c922d6…), Lemma 3.30, p.27

import Mathlib
import Definitions.Def_FuzzyExtractors_Hamming_Basic
import Definitions.Def_LowErrExt_bias
import Definitions.Def_LowErrExt_IsAffineSource

open FuzzyExtractors.Hamming

namespace LowErrExt

/-- **Lemma 3.30 (XOR lemma for ε-biased affine sources), corrected: `ε < 1`.**
Doron, Goodman, *Low-Error Extractors*, STOC 2027 submission (manuscript sha256 43c922d6…),
Lemma 3.30, p.27: "If X ∼ Fn2 is an ε-biased affine source, then X is 2^{n/2}ε-close to an affine
source Z ∼ Fn2 such that for every y ∈ Fn2, bias[IP(X, y)] = 1 =⇒ bias[IP(Z, y)] = 1,
bias[IP(X, y)] ≤ ε =⇒ bias[IP(Z, y)] = 0."

**Formalization Note.** Correction: `ε < 1` is added. As printed (no bound on `ε`), at `ε = 1` every
source is `1`-biased affine and `bias[IP(X, 0)] = 1 ≤ ε`, so the second implication would demand
`bias[IP(Z, 0)] = 0`, while `IP(Z, 0)` is constant and has bias `1`. Correction: `0 ≤ ε` is added.
At `ε < 0` the point mass at `0` is `ε`-biased affine (every bias is `1`), and the distance bound
`2^{n/2}ε` is negative. Closeness is `statDist`. -/
theorem lemma_3_30 {n : ℕ} (X : PMF (Fin n → ZMod 2)) (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hX : IsBiasedAffine ε X) :
    ∃ Z : PMF (Fin n → ZMod 2), IsAffineSource Z ∧
      statDist X Z ≤ (2 : ℝ) ^ ((n : ℝ) / 2) * ε ∧
      ∀ y : Fin n → ZMod 2, (bias X y = 1 → bias Z y = 1) ∧ (bias X y ≤ ε → bias Z y = 0) := by sorry

end LowErrExt
