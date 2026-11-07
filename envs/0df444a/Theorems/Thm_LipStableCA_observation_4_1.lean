-- Prove2me | Theorems.Thm_LipStableCA_observation_4_1
-- name    : LipStableCA.observation_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:51:08.468164+00:00
-- url     : https://prove2.me/theorems/72f8efcd-0daa-4d6d-b3b9-0990bf46f39c
-- title:
--   Observation 4.1 — the law of a discount
-- statement:
--   Fix $0<\epsilon<1$. In the random discount auction (Mechanism 2), for every bidder $i$ and nonempty bundle $B$, the discount $a_{i,B}=1-\epsilon U_{i,B}^{1/m}$ lies in $[1-\epsilon,1]$ and
--   $$\Pr[a_{i,B}>b]=\Bigl(\frac{1-b}{\epsilon}\Bigr)^m\qquad\text{for every }b\in[1-\epsilon,1].$$
--   That is, $a_{i,B}$ has the density $f_m(a)=m(1-a)^{m-1}/\epsilon^m$ on $[1-\epsilon,1]$.
--
--   The vanishing of this density at $a=1$ is what makes the union over $2^m$ bundles affordable in Lemma 4.8.
--
--   Differences from the source:
--   - encoding: $m,n\ge 1$ throughout (§5 says so; Mechanism 2 has $U^{1/m}$) → the hypothesis `1 ≤ m`; reason: the paper's standing setting; excludes only the empty item set
--   - encoding: Pr over the seed of Mechanism 2 → the law `discountMeasure` of the independent uniforms $U_{i,B}$; reason: the discounts are functions of $U$; the coins do not enter these events
-- source:
--   Afshinmehr, Koutsoupias, Lipschitz Stable Combinatorial Auctions, STOC 2027 submission (manuscript sha256 c5e4c53f…), Observation 4.1, p.14

import Definitions.Def_LipStableCA_randomDiscount
open MeasureTheory

namespace LipStableCA

/-- **Observation 4.1.** Afshinmehr, Koutsoupias, *Lipschitz Stable Combinatorial Auctions*, STOC 2027 submission (manuscript sha256 c5e4c53f…), p.14. **Formalization Note.** the hypothesis `1 ≤ m`: the paper's standing setting; excludes only the empty item set. the law `discountMeasure` of the independent uniforms `U_{i,B}`: the discounts are functions of `U`; the coins do not enter these events. -/
theorem observation_4_1 {n m : ℕ} (hm : 1 ≤ m) {ϵ : ℝ} (h0 : 0 < ϵ) (h1 : ϵ < 1) (i : Fin n)
    (B : Finset (Fin m)) (hB : B ≠ ∅) :
    (∀ U : Fin n → Finset (Fin m) → ℝ, (∀ h C, U h C ∈ Set.Icc (0 : ℝ) 1) →
      discount ϵ U i B ∈ Set.Icc (1 - ϵ) 1) ∧
    (∀ b ∈ Set.Icc (1 - ϵ) 1,
      (discountMeasure n m).real {U | b < discount ϵ U i B} = ((1 - b) / ϵ) ^ m) ∧
    (discountMeasure n m).map (fun U => discount ϵ U i B) =
      volume.withDensity fun a => ENNReal.ofReal
        (if a ∈ Set.Icc (1 - ϵ) 1 then (m : ℝ) * (1 - a) ^ (m - 1) / ϵ ^ m else 0) := by sorry

end LipStableCA
