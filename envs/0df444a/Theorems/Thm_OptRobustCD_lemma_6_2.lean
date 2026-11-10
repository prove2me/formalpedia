-- Prove2me | Theorems.Thm_OptRobustCD_lemma_6_2
-- name    : OptRobustCD.lemma_6_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:52:15.501304+00:00
-- url     : https://prove2.me/theorems/fbad7089-7b0a-472b-a23a-27690f296763
-- title:
--   Lemma 6.2 (a)–(c) — estimates for the corrected Bethe Hessian: $b^\top Hb/n\to c<0$, $\|(M_s+gI)\sigma^{(s)}\|\le\varepsilon\|\sigma^{(s)}\|$, $\|\sigma^{(s)}\|_4^4\le\frac Cn\|\sigma^{(s)}\|^4$
-- statement:
--   Let $d>0$, $\lambda\in(-1,1)$ with $d\lambda^2>1$, $(G,\sigma^\star)\sim\mathrm{SBM}(n,d,\lambda)$, and $t$, $H=H(t)$, $b$, $M_s$ as in Definition 5.5 with the constant $L$ large enough. Then:
--
--   1. (a) If $\lambda>0$, then $\frac1n b^\top Hb$ converges in probability to a negative constant.
--   2. (b) There is $g=g(d,\lambda)>0$ such that for every $\varepsilon>0$ there is $s_0$ such that for every $s\ge s_0$, with high probability, $\|(M_s+gI)\sigma^{(s)}\|\le\varepsilon\|\sigma^{(s)}\|$.
--   3. (c) There is $C=C(d,\lambda)$ such that for every $s$, with high probability, $\|\sigma^{(s)}\|_4^4\le\frac Cn\|\sigma^{(s)}\|^4$.
--
--   These are the scalar estimates behind Lemma 5.6.
--
--   Differences from the source:
--   - reading: L = L(d,λ) ⩾ 2 a sufficiently large constant (Definition 5.5) → ∃ L₀ ⩾ 2, ∀ L ⩾ L₀; reason: the meaning of 'sufficiently large'
--   - encoding: converges in probability to c → ∀ δ > 0, w.h.p. |b^⊤Hb/n − c| ⩽ δ; reason: the meaning of convergence in probability
--   - encoding: with high probability → the SBM(n,d,λ) probability of the event tends to 1 (Whp); reason: the meaning of the phrase
--   - encoding: quotients the source writes only where they are defined → Lean's x/0 = 0 at a zero denominator; reason: changes no instance where the source's quotient is defined; on the high-probability event the denominators are nonzero
-- source:
--   Hopkins, Hua, Mohanty, Rajaraman, Steurer, Optimal Robust Community Detection, STOC 2027 submission (manuscript of November 3, 2026, sha256 3d287d5422db7c4a43e74333bda1dbed204af51a25fd9f2c6e875ae03a4dafa1), Lemma 6.2, p.29 (pdf p.31)

import Mathlib
import Definitions.Def_OptRobustCD_Whp
import Definitions.Def_OptRobustCD_BetheHessian

namespace OptRobustCD

/-- **Lemma 6.2** (Estimates for the corrected Bethe Hessian), parts (a), (b) and (c). Hopkins,
Hua, Mohanty, Rajaraman, Steurer, *Optimal Robust Community Detection*, STOC 2027 submission
(manuscript of November 3, 2026, sha256 3d287d54…), Lemma 6.2, p.29 (pdf p.31).

"(a) If λ > 0, then `(1/n) b^⊤Hb` converges in probability to a negative constant.
(b) There is a constant g = g(d, λ) > 0 such that for every ε > 0 there is `s_0` such that for every
`s ⩾ s_0`, with high probability, `∥(M_s + gI)σ^{(s)}∥ ⩽ ε∥σ^{(s)}∥`.
(c) There is C = C(d, λ) such that for every s, with high probability
`∥σ^{(s)}∥⁴_4 ⩽ (C/n)∥σ^{(s)}∥⁴`."

**Formalization Note.**
* Standing assumptions of §6 (p.28): `dλ² > 1`, and `t, H = H(t), b, M_s` as in Definition 5.5,
  where `L = L(d, λ) ⩾ 2` is "a sufficiently large constant": the statement holds for every
  `L ⩾ L₀` for some `L₀ ⩾ 2`. Of §3.1: `d > 0`, `λ ∈ (−1, 1)`, `(G, σ⋆) ∼ SBM(n, d, λ)`.
* "(1/n) b^⊤Hb converges in probability to `c`": for every `δ > 0`, with high probability
  `|b^⊤Hb/n − c| ⩽ δ`.
* All three parts are in this one item. -/
theorem lemma_6_2 (d lam : ℝ) (hd : 0 < d) (hlam : lam ∈ Set.Ioo (-1 : ℝ) 1)
    (hKS : 1 < d * lam ^ 2) :
    ∃ L₀ : ℕ, 2 ≤ L₀ ∧ ∀ L : ℕ, L₀ ≤ L →
      (0 < lam → ∃ c : ℝ, c < 0 ∧ ∀ δ : ℝ, 0 < δ → Whp d lam (fun n _σ G =>
        |(bVec d lam L G ⬝ᵥ (betheH G (tPar d lam)).mulVec (bVec d lam L G)) / n - c| ≤ δ)) ∧
      (∃ g : ℝ, 0 < g ∧ ∀ ε : ℝ, 0 < ε → ∃ s₀ : ℕ, ∀ s : ℕ, s₀ ≤ s → Whp d lam (fun _n σ G =>
        l2 ((Ms d lam L s G + g • (1 : Matrix _ _ ℝ)).mulVec (sigmaS d lam s G σ)) ≤
          ε * l2 (sigmaS d lam s G σ))) ∧
      (∃ C : ℝ, ∀ s : ℕ, Whp d lam (fun n σ G =>
        l4pow4 (sigmaS d lam s G σ) ≤ C / n * l2 (sigmaS d lam s G σ) ^ 4)) := by sorry

end OptRobustCD
