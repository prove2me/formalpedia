-- Prove2me | Theorems.Thm_MulticlassOmni_Lipschitz_theorem_4_1
-- name    : MulticlassOmni.Lipschitz.theorem_4_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T22:10:30.810421+00:00
-- url     : https://prove2.me/theorems/bd798db4-81f6-4cb6-a164-293d06d6fa8d
-- title:
--   Theorem 4.1 — batch multiclass omniprediction for Lipschitz proper losses needs $n\ge(Ck\varepsilon\log(1/\varepsilon))^{-(k+2)/4}$ samples (tail and expected pseudo-regret)
-- statement:
--   There are absolute constants $c,C>0$ such that, for every integer $k\ge3$ and every $0<\varepsilon<c/(k\log(k+1))$, there are a finite non-empty domain $X\subseteq\Delta_k$ and two distinct benchmarks $f_1,f_2:X\to\Delta_k$, $F=\{f_1,f_2\}$, such that the following holds for every $n\ge0$ and every randomized learner that receives $n$ i.i.d. samples from a distribution $D$ on $X\times[k]$ and outputs one predictor $p:X\to\Delta_k$, $p\sim P_D$:
--   1. if $\mathrm{OR}^{(\varepsilon)}_D(P_D;L_{\mathrm{lip\text{-}proper}},F)\le\frac14$ for every distribution $D$ (14), then $n\ge(Ck\varepsilon\log(1/\varepsilon))^{-(k+2)/4}$;
--   2. if $\mathrm{OR}_D(P_D;L_{\mathrm{lip\text{-}proper}},F)\le\varepsilon$ for every distribution $D$, then $n\ge(Ck\varepsilon\log(1/\varepsilon))^{-(k+2)/4}$.
--
--   Here $\mathrm{OR}^{(\varepsilon)}_D(P;L,F)=\sup_{\ell\in L}\max_{f\in F}\Pr_{p\sim P}[R_D(p,\ell,f)>\varepsilon]$ and $\mathrm{OR}_D(P;L,F)=\sup_{\ell\in L}\max_{f\in F}\mathbb E_{p\sim P}[R_D(p,\ell,f)]$ with $R_D(p,\ell,f)=\mathbb E_{(x,y)\sim D}[\ell(p(x),y)-\ell(f(x),y)]$; logarithms are natural; the same $X$, $f_1$, $f_2$ serve both clauses and do not depend on $n$, the learner or $D$.
--
--   Differences from the source:
--   - encoding: a randomized learner receiving n i.i.d. samples, with output law P_D → for each data set S an arbitrary probability measure A(S) on predictors X → Δ_k (Borel structure of the closed simplex), and P_D = ∑_S (∏_j D(S_j)) A(S); reason: this is exactly a learner whose private randomness is independent of D given S; continuous randomization is allowed
--   - encoding: X a finite domain (non-empty by §2) and a class of two benchmarks F = {f1, f2} → X : Finset (Fin k → ℝ) with X.Nonempty and X ⊆ stdSimplex, f₁ f₂ : X → Δ_k with f₁ ≠ f₂, F = {f₁, f₂}; reason: makes §2's standing non-emptiness and the count 'two' explicit; same instances
--   - encoding: D ∈ Δ(X × [k]) → D : X × Fin k → ℝ, nonnegative with total mass 1 (IsDist); reason: finite support; same objects
--   - encoding: sup_ℓ max_f of probabilities and of expectations → suprema in ℝ≥0∞ (tailOmniRegret) and in EReal (pseudoOmniRegret); reason: genuine suprema with no junk value; the family contains the zero loss and the regret is bounded
--   - encoding: a loss ℓ : Δ_k × [k] → ℝ and properness E_{y∼q}ℓ(q,y) ≤ E_{y∼q}ℓ(r,y) → a total ℓ : ℝ^k → Fin k → ℝ constrained only on stdSimplex; properness is the published UCalibDirichlet.IsProperLoss of its EReal embedding, extended by 0 off the simplex; reason: values off the simplex are never read; for real values the predicate's 'never −∞' clause is automatic, so the instances are the same
--   - encoding: labels [k] = {1, …, k} → Fin k, the source label y is the index y − 1 (label 1 is index 0); reason: relabeling; same instances
-- source:
--   Hu, Luo, Schneider, Yang (2026), Sample Complexity of Multiclass Omniprediction, supplied PDF (SHA-256 aaa73474…584f0, citation basis published; STOC 2027 submission), Theorem 4.1, p. 15 (continues p. 16)

import Mathlib
import Definitions.Def_MulticlassOmni_Lipschitz_ProperLosses
import Definitions.Def_MulticlassOmni_Lipschitz_OmniRegret

open MeasureTheory

namespace MulticlassOmni.Lipschitz

/-- **Theorem 4.1 (Batch pseudo regret)**, Hu, Luo, Schneider, Yang (2026), pp. 15–16.
There are absolute constants `c, C > 0` such that for every integer `k ≥ 3` and every
`0 < ε < c / (k log(k+1))` there are a finite nonempty domain `X ⊆ Δ_k` and two distinct
benchmarks `f₁, f₂ : X → Δ_k` such that, for every sample size `n` and every randomized learner
with `n` i.i.d. examples whose output law under `D` is `P_D`:
* if `OR^{(ε)}_D(P_D; L_lip-proper, {f₁, f₂}) ≤ 1/4` for every distribution `D` on `X × [k]`,
  then `n ≥ (C k ε log(1/ε))^{-(k+2)/4}`; and
* if `OR_D(P_D; L_lip-proper, {f₁, f₂}) ≤ ε` for every `D`, then the same bound holds. -/
theorem theorem_4_1 :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ k : ℕ, 3 ≤ k → ∀ ε : ℝ, 0 < ε → ε < c / ((k : ℝ) * Real.log ((k : ℝ) + 1)) →
        ∃ X : Finset (Fin k → ℝ), X.Nonempty ∧ (∀ x ∈ X, x ∈ stdSimplex ℝ (Fin k)) ∧
          ∃ f₁ f₂ : Predictor X, f₁ ≠ f₂ ∧
            ∀ n : ℕ, ∀ A : Learner X n,
              ((∀ D : ↥X × Fin k → ℝ, IsDist D →
                  tailOmniRegret D (outputLaw A D) (lipProperFamily k) {f₁, f₂} ε ≤ 1 / 4) →
                (C * k * ε * Real.log (1 / ε)) ^ (-((k : ℝ) + 2) / 4) ≤ (n : ℝ)) ∧
              ((∀ D : ↥X × Fin k → ℝ, IsDist D →
                  pseudoOmniRegret D (outputLaw A D) (lipProperFamily k) {f₁, f₂} ≤ (ε : EReal)) →
                (C * k * ε * Real.log (1 / ε)) ^ (-((k : ℝ) + 2) / 4) ≤ (n : ℝ)) := by sorry

end MulticlassOmni.Lipschitz
