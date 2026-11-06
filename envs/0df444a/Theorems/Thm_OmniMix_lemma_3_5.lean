-- Prove2me | Theorems.Thm_OmniMix_lemma_3_5
-- name    : OmniMix.lemma_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:47:12.72528+00:00
-- url     : https://prove2.me/theorems/37139506-56fb-463c-ab71-86bcbae1e49f
-- title:
--   Lemma 3.5 — second-order regret bound for Algorithm 2
-- statement:
--   Let $F$ be a finite class of maps $X\to[0,1]$, $T$ a horizon, $0<\eta\le1/2$, $\beta>0$, and let $\ell$ be a proper $\beta$-mixable loss with a V-shaped representation $\ell(p,y)=C(y)+\int_0^1w(v)\lambda_v(p,y)\,dv$ ($C$ real, $w\ge0$ measurable). Let $\delta=1/(2(T+1))$, $M_\delta=2\log(2T+1)$, and let $D_1,\dots,D_T$ be a run of Algorithm 2 on a context–outcome sequence $(x_t,y_t)$. Then for every $f\in F$,
--   $$
--   \sum_{t=1}^T\int_{I_\delta}w(v)\,z_{t,f,v}\,dv\le\frac{M_\delta\,[\log(e|F|)+1/e]}{\beta\eta}+\eta\sum_{t=1}^T\mathbb E_{P\sim D_t}\int_{I_\delta}w(v)\,P(1-P)\,b_v(P,f(x_t))^2\,dv,
--   $$
--   where $z_{t,f,v}=\mathbb E_{P\sim D_t}[b_v(P,f(x_t))(y_t-P)]$.
--
--   The first term is the complexity of the continuous exponential weights over $F\times I_\delta$; the second is the Bernoulli-variance term that Lemma 3.6 cancels against the properness gain.
--
--   Differences from the source:
--   - reading: O(log(T) log(|F|)/(βη)) → M_δ[log(e|F|) + 1/e]/(βη) with M_δ = 2 log(2T+1); reason: the proof (p.31) proves this term and identifies it with the printed O for T ≥ 2, |F| ≥ 2; the printed O would be 0 at |F| = 1
--   - reading: w_ℓ, the density of Lemma 2.1 → w, the density of any representation (13) with real constants; reason: the density is unique a.e.; a mixable loss with such a representation is never −∞ and finite on (0,1) (real C_ℓ(0) = ℓ(0,0), C_ℓ(1) = ℓ(1,1), and properness plus mixability exclude an interior +∞), so the correction of Lemma 2.1 is carried by this hypothesis
--   - encoding: Algorithm 2 with an EVI solver → any forecast sequence satisfying Algorithm 2's support and EVI conditions in every round (IsAlg2Run); reason: the analysis uses only these conditions
-- source:
--   Liu–Luo–Ratliff, Omniprediction for All Mixable Proper Losses and Beyond, arXiv:2610.41023, Lemma 3.5, p.14 (PDF p.16); explicit term from its proof, App. B, p.31 (PDF p.33)

import Mathlib
import Definitions.Def_OmniMix_IsProper
import Definitions.Def_OmniMix_IsMixable
import Definitions.Def_OmniMix_HasVRep
import Definitions.Def_OmniMix_IsAlg2Run
import Definitions.Def_OmniMix_Mdelta

namespace OmniMix

/-- **Lemma 3.5 (second-order regret bound for Algorithm 2).** Liu–Luo–Ratliff, arXiv:2610.41023, §3.2, p.14 (proof App. B,
pp.30–31): "If `ℓ` is proper and β-mixable, then for any `f ∈ F`, Algorithm 2 satisfies
`Σ_{t=1}^T ∫_{I_δ} w_ℓ(v) z_{t,f,v} dv ≤ O(log(T) log(|F|)/(βη)) + η Σ_{t=1}^T E_{P∼D_t} ∫_{I_δ} w_ℓ(v)P(1 − P)b_v(P, f(x_t))² dv`."

The `O(·)` term is stated as the explicit complexity term of the proof (p.31):
`M_δ[log(e|F|) + 1/e]/(βη)`, with `M_δ = 2 log(2T + 1)`.

**Formalization Note.** `w` is the density of any representation (13) of `ℓ` (Lemma 2.1). A run of
Algorithm 2 is `IsAlg2Run` (`δ = 1/(2(T+1))`, `ϵ_t = 1/T`), with `0 < η ≤ 1/2`. A representation
(13) with real constants already makes `ℓ` never `−∞` and, with mixability, finite on `(0,1)`, so
the correction of Lemma 2.1 needs no separate hypothesis here. Rounds are 0-based; `T = 0` is the
empty run. -/
theorem lemma_3_5 {X : Type*} (F : Finset (X → unitInterval)) (T : ℕ) (η : ℝ) (hη0 : 0 < η)
    (hη1 : η ≤ 1 / 2) (β : ℝ) (hβ : 0 < β) (ℓ : Loss) (hprop : IsProper ℓ)
    (hmix : IsMixable β ℓ) (C : Bool → ℝ) (w : ℝ → ENNReal) (hrep : HasVRep ℓ C w)
    (x : Fin T → X) (y : Fin T → Bool) (D : Fin T → FinDist) (hrun : IsAlg2Run F T η x y D)
    (f : X → unitInterval) (hf : f ∈ F) :
    ∑ t, ∫ v in Idelta (deltaT T), (w v).toReal * alg2Reward x y D t f v ≤
      Mdelta T * (Real.log (Real.exp 1 * (F.card : ℝ)) + Real.exp (-1)) / (β * η) +
        η * ∑ t, (D t).expectR (fun P => ∫ v in Idelta (deltaT T),
          (w v).toReal * ((P : ℝ) * (1 - P) * bV v P (f (x t)) ^ 2)) := by sorry

end OmniMix
