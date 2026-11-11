-- Prove2me | Theorems.Thm_GrothendieckPD_Digits_lemma_2_1
-- name    : GrothendieckPD.Digits.lemma_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:06:23.90252+00:00
-- url     : https://prove2.me/theorems/4b58dfe8-f826-40c2-a589-b41838a98ff8
-- title:
--   Lemma 2.1: $K_G^{-1}\ge c_1(\mu)-\sum_{\mathrm{odd}\ m\ge3}|c_m(\mu)|$
-- statement:
--   Let $n\in\mathbb N$ and let $\mu$ be a distribution on pairs of odd measurable functions $f,g:\mathbb R^n\to\{\pm1\}$, with coefficients $c_m(\mu)=\mathbb E_{(f,g)\sim\mu}\langle\Pi_mf,\Pi_mg\rangle$. Then
--   $$K_G^{-1}\ \ge\ c_1(\mu)-\sum_{\text{odd }m\ge3}|c_m(\mu)| ,$$
--   where $K_G$ is the real Grothendieck constant of Eq. (1.1).
--
--   This is the Krivine rounding bound: every odd rounding scheme certifies an upper bound on $K_G$.
--
--   Differences from the source:
--   - reading: odd functions f, g : ℝⁿ → {±1} → f(−x) = −f(x) for γₙ-almost every x; reason: pointwise oddness is impossible for ±1-valued functions (f(0) = −f(0)); a.e. oddness is the only satisfiable meaning and every Hermite coefficient depends only on the a.e. class
--   - encoding: f, g : ℝⁿ → {±1} → measurable functions with values in {1, −1} (GrothendieckLB.IsSignFn); reason: Hermite coefficients require measurability; the source states it in Lemma 2.5 and uses it throughout
--   - reading: a distribution µ on pairs of functions → a jointly measurable random pair (F, G) over a probability space (Ω, µ) (GrothendieckLB.MixedScheme); reason: the source fixes no σ-algebra on a space of functions; the random-pair reading contains every finite mixture and makes ω ↦ c_m(F ω, G ω) measurable
--   - encoding: c_m(f, g) = ⟨Π_m f, Π_m g⟩ → the moment sum ∑_{|α| = m} E[f He_α] E[g He_α] / α! (GrothendieckLB.pmInner); reason: same value by orthonormality of ψ_α = He_α/√α!
--   - encoding: K_G = sup_{m,n} sup_{A} SDP(A)/OPT(A) (Eq. 1.1) → K_G = inf{K : SDP(A) ≤ K·OPT(A) for all real matrices A} (published GrothendieckConstant.grothendieckConst), with unit vectors in ℝ^d for arbitrary d; reason: same value: the ratio is undefined only at A = 0, where both sides vanish; OPT(A) > 0 for A ≠ 0; the admissible set is nonempty (Grothendieck's inequality) and bounded below; unit vectors in any dimension give the same SDP value as in ℝ^{m+n}
--   - encoding: the sum over odd degrees m ≥ 3 → the sum over k : ℕ with m = 2*k + 3; reason: a bijective reindexing of every odd degree at least 3
-- source:
--   Steven Heilman, Chris Jones, Giulio Malavolta, Primal/Dual Method for the Grothendieck Constant, STOC 2027 submission #820 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/820.pdf, Lemma 2.1, p. 4

import Mathlib
import Definitions.Def_GrothendieckPD_Digits_FiniteGames

namespace GrothendieckPD.Digits

/-- Lemma 2.1 (p. 4). For every `n` and every distribution `µ` on pairs of odd functions
`f, g : ℝ^n → {±1}`, `K_G^{-1} ≥ c_1(µ) - ∑_{odd m ≥ 3} |c_m(µ)|`. -/
theorem lemma_2_1 (n : ℕ) (S : GrothendieckLB.MixedScheme n) (hS : IsOddScheme S) :
    krivineValue (schemeCoeff S) ≤ (GrothendieckConstant.grothendieckConst)⁻¹ := by sorry

end GrothendieckPD.Digits
