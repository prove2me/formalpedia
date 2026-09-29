-- Prove2me | Theorems.Thm_FranklKupavskii2022_EMC_very_big_vs_just_big
-- name    : FranklKupavskii2022.EMC.very_big_vs_just_big
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T13:20:20.546655+00:00
-- url     : https://prove2.me/theorems/35c2a1c6-0e2e-4e51-a08d-f3b2b75b8b8d
-- title:
--   Proposition 13: $\Pr[\eta\ge4Ct]\le2e^{-C^2t/2}\Pr[|\eta-2Ct|\le Ct]$
-- statement:
--   In the setting of Theorem 12 ($m\ge tl$, $\mathcal G\subseteq\binom{[m]}l$ of density $\alpha$, $\eta=|\mathcal G\cap\mathcal B|$ for a uniformly random $t$-matching $\mathcal B$), assume $\mathbb E[\eta]=\alpha t$. Let $C$ be a constant with
--
--   $$
--   0<C\le\tfrac12,\qquad C\ge\alpha,\qquad C^2t\ge16 .
--   $$
--
--   Then
--
--   $$
--   \Pr[\eta\ge4Ct]\le2e^{-C^2t/2}\,\Pr\big[|\eta-2Ct|\le Ct\big]. \tag{24}
--   $$
--
--   The proposition compares the probability that $\eta$ is "very big" with the probability that it is "just big"; it replaces Theorem 12 in the proof of Lemma 15 when the density $\alpha$ is small.
--
--   **Formalization Note** The hypothesis $\mathbb E[\eta]=\alpha t$ is kept as in the paper, although it always holds.
-- source:
--   Frankl–Kupavskii, The Erdős Matching Conjecture and concentration inequalities, arXiv:1806.08855v3, Proposition 13, p. 8

import Mathlib
import Definitions.Def_FranklKupavskii2022_EMC_tMatchings

namespace FranklKupavskii2022.EMC

/-- Proposition 13 (Frankl–Kupavskii, arXiv:1806.08855v3, p. 8): in the notations above (Lemma 10,
Theorem 12), assume that `E[η] = αt`. Fix a constant `0 < C ≤ 1/2` such that `C ≥ α` and
`C²t ≥ 16`. Then `Pr[η ≥ 4Ct] ≤ 2e^{−C²t/2} Pr[|η − 2Ct| ≤ Ct]` (24).

**Formalization Note.** The hypothesis `E[η] = αt` is kept as stated although (16) makes it
automatic. `B` is uniform on `tMatchings m l t`, nonempty since `t * l ≤ m`; `C²t ≥ 16` forces
`t ≥ 1`. -/
theorem very_big_vs_just_big (m l t : ℕ) (hm : t * l ≤ m) (G : Finset (Finset ℕ))
    (hG : G ⊆ (Finset.Icc 1 m).powersetCard l)
    (hE : avg m l t (fun B => (eta G B : ℝ)) = density m l G * t)
    (C : ℝ) (hC0 : 0 < C) (hC1 : C ≤ 1 / 2) (hCα : density m l G ≤ C) (hCt : 16 ≤ C ^ 2 * t) :
    prob m l t (fun B => 4 * C * t ≤ (eta G B : ℝ)) ≤
      2 * Real.exp (-(C ^ 2 * t) / 2) *
        prob m l t (fun B => |(eta G B : ℝ) - 2 * C * t| ≤ C * t) := by sorry

end FranklKupavskii2022.EMC
