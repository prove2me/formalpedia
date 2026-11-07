-- Prove2me | Theorems.Thm_KTCenter_lemma_4_4
-- name    : KTCenter.lemma_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:28:31.458932+00:00
-- url     : https://prove2.me/theorems/c07e15cf-07fe-4bf7-8f5e-2109ce4bd914
-- title:
--   Lemma 4.4 with (11) — a minimum-cost ordering of the §4.3 tournament has radius $\le(1+2\delta)R^*$
-- statement:
--   Relabel so that $\rho=\pi_1=(1,\dots,d)$; fix an optimal center $\sigma^*$ and an index set $J$, and let $T$ order each pair of $E_J$ as $\sigma^*$ and every other pair as $\rho$. Then:
--
--   1. for every ranking $y$ and every $i$, (11):
--   $$\mathcal K(y,\pi_i)-\mathcal K(\sigma^*,\pi_i)\le c_T(y)-c_T(\sigma^*)+2|U_J\cap\mathrm{Inv}(\pi_i)|;$$
--   2. if $\delta>0$ and $J$ satisfies (10), then every $\tau$ minimizing $c_T$ has $\mathrm{Obj}(\Pi,\tau)\le(1+2\delta)R^*$.
--
--   The tournament may contain cycles, so $\tau$ need not agree with $T$; the lemma bounds its radius anyway.
--
--   Differences from the source:
--
--   - encoding: candidates relabeled by their position in the first input, so ρ = π₁ = (1, …, d) (§4.1) → hypothesis `I.π I.first = 1` on the input list; reason: the relabeling preserves all distances and is undone at the end (p.17); the statements of §§4–5 are about relabeled inputs
--   - generalization: (11) for the J of Theorem 4.3 → (11) for every index set J; reason: the proof of (11) uses only that T differs from σ* exactly on U_J, which holds for every J; it specializes to the source
-- source:
--   Chakraborty, Das, Mukherjee, Kendall–tau Center Admits a PTAS, STOC 2027 submission (manuscript sha256 4739ffba…), Lemma 4.4 and eq. (11), p.19 (PDF p.21)

import Mathlib
import Definitions.Def_KTCenter_Instance
import Definitions.Def_KTCenter_InversionUnion
import Definitions.Def_KTCenter_Tournament

namespace KTCenter

/-- **Lemma 4.4** (Minimum-cost tournament ordering), p.19 (PDF p.21), with eq. (11).

Chakraborty, Das, Mukherjee, *Kendall–tau Center Admits a PTAS*, STOC 2027 submission (manuscript
sha256 4739ffba…).

**Formalization Note.** On relabeled inputs, `π₁ = 1` (§4.1); `T` is the tournament of §4.3 for `E_J`
and the optimal center `σ*`. Eq. (11) holds for every `y`, `i` and is stated in `ℤ`. The lemma's
hypothesis "J satisfies (10)" is the premise on `J`. -/
theorem lemma_4_4 (I : Instance) (hρ : I.π I.first = 1) (σs : Equiv.Perm (Fin I.d))
    (hσ : obj I σs = optRadius I) (J : Finset (Fin I.n)) :
    (∀ (y : Equiv.Perm (Fin I.d)) (i : Fin I.n),
      (dist y (I.π i) : ℤ) - dist σs (I.π i) ≤
        ((centerTournament (EJ I J) σs).cost y : ℤ) - (centerTournament (EJ I J) σs).cost σs +
          2 * (((UJ I J σs) ∩ Inv (I.π i)).card : ℤ)) ∧
    ∀ δ : ℝ, 0 < δ →
      (∀ i : Fin I.n, (((UJ I J σs) ∩ Inv (I.π i)).card : ℝ) ≤ δ * (optRadius I : ℝ)) →
      ∀ τ : Equiv.Perm (Fin I.d),
        (∀ ω, (centerTournament (EJ I J) σs).cost τ ≤ (centerTournament (EJ I J) σs).cost ω) →
        (obj I τ : ℝ) ≤ (1 + 2 * δ) * (optRadius I : ℝ) := by sorry

end KTCenter
