-- Prove2me | Theorems.Thm_OmniMix_app_A3_bound
-- name    : OmniMix.app_A3_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:46:58.325032+00:00
-- url     : https://prove2.me/theorems/5e95006c-feb3-4266-b376-af1c96218b36
-- title:
--   Proof of Theorem 1.2, App. A.3 — Algorithm 2's bound for any learning rate (corrected: ℓ finite on (0,1))
-- statement:
--   There is an absolute constant $K>0$ such that the following holds. Let $F$ be a finite class of maps $X\to[0,1]$, $T$ a horizon, $0<\eta\le1/2$, $\beta>0$, and $\ell$ a proper $\beta$-mixable loss, never $-\infty$ and finite on $(0,1)$. Let $\delta=1/(2(T+1))$, $M_\delta=2\log(2T+1)$, and let $D_1,\dots,D_T$ be a run of Algorithm 2 on a context–outcome sequence $(x_t,y_t)$. Then for every $f\in F$,
--   $$
--   \sum_{t=1}^T\mathbb E_{P\sim D_t}[\ell(P,y_t)]-\sum_{t=1}^T\ell(f(x_t),y_t)\le\frac K\beta\Big(\frac{M_\delta\log(e|F|)}{\eta}+T\eta^2+T\delta\Big).
--   $$
--
--   Choosing $\eta=\min\{1/2,(M_\delta\log(e|F|)/T)^{1/3}\}$ in this bound gives Theorem 1.2.
--
--   Differences from the source:
--   - reading: O((1/β)(M_δ log(e|F|)/η + Tη² + Tδ)) → K·(M_δ log(e|F|)/η + Tη² + Tδ)/β with one absolute K > 0 chosen before all other quantities; reason: the O hides an absolute constant, independent of F, T, η, β, ℓ
--   - correction: β-mixable proper loss → also finite on (0,1) and never −∞; reason: same correction as Lemma 2.1: ℓ(q,0) = q, ℓ(q,1) = +∞ is proper and mixable but has no representation (13) with real C_ℓ, on which this result's proof rests; −∞ is outside the paper's codomain
--   - encoding: Σ_t E_{P∼D_t}[ℓ(P,y_t) − ℓ(f(x_t),y_t)] → difference of the two sums in ℝ∪{±∞}; reason: equal when the benchmark losses are finite; −∞ when one is +∞, the paper's convention (p.31)
-- source:
--   Liu–Luo–Ratliff, Omniprediction for All Mixable Proper Losses and Beyond, arXiv:2610.41023, proof of Theorem 1.2, App. A.3, p.24 (PDF p.26)

import Mathlib
import Definitions.Def_OmniMix_IsProper
import Definitions.Def_OmniMix_IsMixable
import Definitions.Def_OmniMix_IsAlg2Run
import Definitions.Def_OmniMix_Mdelta
import Definitions.Def_OmniMix_FinDist_expect

namespace OmniMix

universe u

/-- **Algorithm 2's bound for any learning rate (proof of Theorem 1.2).** Liu–Luo–Ratliff, arXiv:2610.41023, App. A.3, p.24: "The
learning rate `0 < η ≤ 1/2` and predictor `f ∈ F` are arbitrary and fixed. Averaging Lemma 3.7 and
Lemma 3.6 over `D_t` and applying Lemma 3.5 gives
`Σ_{t=1}^T E_{P∼D_t}[ℓ(P, y_t) − ℓ(f(x_t), y_t)] ≤ O((1/β)(M_δ log(e|F|)/η + Tη² + Tδ))`."

Stated with one absolute constant `K`: for every finite `F`, horizon `T`, `η ∈ (0,1/2]`, `β > 0`,
proper β-mixable loss (finite on `(0,1)`, never `−∞`), run of Algorithm 2 and `f ∈ F`,
`Σ_t E_{D_t}ℓ(P,y_t) − Σ_t ℓ(f(x_t),y_t) ≤ K(M_δ log(e|F|)/η + Tη² + Tδ)/β`.

**Formalization Note.** Computed in `EReal`; if some `ℓ(f(x_t), y_t) = +∞` the left side is `−∞`.
`δ = deltaT T`, `M_δ = Mdelta T`. The constant `K` is quantified before everything else. -/
theorem app_A3_bound : ∃ K : ℝ, 0 < K ∧ ∀ {X : Type u} (F : Finset (X → unitInterval)) (T : ℕ)
    (η : ℝ), 0 < η → η ≤ 1 / 2 → ∀ β : ℝ, 0 < β → ∀ ℓ : Loss, IsProper ℓ →
    (∀ p y, ℓ p y ≠ ⊥) → (∀ p : unitInterval, 0 < (p : ℝ) → (p : ℝ) < 1 → ∀ y, ℓ p y ≠ ⊤) →
    IsMixable β ℓ → ∀ (x : Fin T → X) (y : Fin T → Bool) (D : Fin T → FinDist),
    IsAlg2Run F T η x y D → ∀ f ∈ F,
      (∑ t, (D t).expect (fun P => ℓ P (y t))) - ∑ t, ℓ (f (x t)) (y t) ≤
        ((K * (Mdelta T * Real.log (Real.exp 1 * (F.card : ℝ)) / η + T * η ^ 2 + T * deltaT T) / β
          : ℝ) : EReal) := by sorry

end OmniMix
