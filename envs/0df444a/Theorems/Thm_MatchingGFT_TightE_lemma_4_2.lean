-- Prove2me | Theorems.Thm_MatchingGFT_TightE_lemma_4_2
-- name    : MatchingGFT.TightE.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:52:22.665629+00:00
-- url     : https://prove2.me/theorems/314d6e41-7a98-44cb-aea8-2c36ca4d8cca
-- title:
--   Lemma 4.2 — Capped-exponential calculations (corrected: φ(0) = −∞, ψ(L) = +∞ in (10))
-- statement:
--   For $L\ge2$ the capped-exponential laws are regular. Almost surely $\phi,\psi$ equal the source's representatives (10). On all of $[0,L]$, $\phi(v)=v-1$ for $0<v<L$, $\phi(L)=L$, $\phi(0)=-\infty$; $\psi(0)=0$, $\psi(c)=c+1$ for $0<c<L$, $\psi(L)=+\infty$. The identity (11) holds on $[0,L]$ in the extended reals, and $g_L=Le^{-L}$, $p_L^S=p_L^B=e^{-L}(1+(L-2)/e)$.
--
--   Differences from the source:
--   - correction: (10) gives φ(0) = −1 and ψ(L) = L + 1 for the functions of PDF p. 10 → φ(0) = −∞ and ψ(L) = +∞, the printed formulas everywhere else on [0, L], plus almost-sure equality with the printed (10); reason: at any L ≥ 2, Q_B(ρ) > 0 and Q_S(σ) < L for all ranks, so the defining sets on PDF p. 10 are empty at v = 0 and c = L; the source’s word “representatives” covers this null-set change, and the Lean statement implies it
--   - encoding: K^lin convex on [0, 1], K(1) a left limit that may be +∞ → K^lin convex on [0, 1); reason: the value at 1 is the left limit of the curve, so convexity on [0, 1) is equivalent
--   - encoding: the arithmetic of (11) at z = 0 → EReal, where L − (−∞) = +∞; reason: both sides are +∞ at z = 0
-- source:
--   Xiaohui Bei, Wenhao Wu, Shengwei Zhou, STOC 2027 submission #465 (October 2026), Lemma 4.2, PDF p. 19; definitions PDF p. 10

import Mathlib
import Definitions.Def_MatchingGFT_TightE_Quantile
import Definitions.Def_MatchingGFT_TightE_Regularity
import Definitions.Def_MatchingGFT_TightE_CappedExp

open MeasureTheory Set

namespace MatchingGFT.TightE

/-- Lemma 4.2 (PDF p. 19), `L ≥ 2`, with the endpoint values of (10) corrected. The capped-exponential laws
are regular. The virtual functions of p. 10 equal the source's representatives (10) almost surely, and on
all of `[0, L]` they are those formulas except `φ(0) = -∞` and `ψ(L) = +∞`, the source's empty-set
values. The mirror identity (11) holds on `[0, L]`, and `g_L = L e^{-L}`, `p_L^S = p_L^B = e^{-L}(1 + (L-2)/e)`. -/
theorem lemma_4_2 (L : ℝ) (hL : 2 ≤ L) :
    IsRegularBuyerLaw (cappedBuyerLaw L) ∧ IsRegularSellerLaw (cappedSellerLaw L) ∧
    (∀ᵐ v ∂cappedBuyerLaw L, virtualValue (cappedBuyerLaw L) v =
      if v < L then ((v - 1 : ℝ) : EReal) else ((L : ℝ) : EReal)) ∧
    (∀ᵐ c ∂cappedSellerLaw L, virtualCost (cappedSellerLaw L) c =
      if c = 0 then 0 else ((c + 1 : ℝ) : EReal)) ∧
    (∀ v ∈ Icc (0 : ℝ) L, virtualValue (cappedBuyerLaw L) v =
      if v = 0 then ⊥ else if v < L then ((v - 1 : ℝ) : EReal) else ((L : ℝ) : EReal)) ∧
    (∀ c ∈ Icc (0 : ℝ) L, virtualCost (cappedSellerLaw L) c =
      if c = 0 then 0 else if c < L then ((c + 1 : ℝ) : EReal) else ⊤) ∧
    (∀ z ∈ Icc (0 : ℝ) L, virtualCost (cappedSellerLaw L) (L - z) =
      ((L : ℝ) : EReal) - virtualValue (cappedBuyerLaw L) z) ∧
    cappedG L = L * Real.exp (-L) ∧
    cappedPS L = Real.exp (-L) * (1 + (L - 2) / Real.exp 1) ∧
    cappedPB L = Real.exp (-L) * (1 + (L - 2) / Real.exp 1) := by sorry

end MatchingGFT.TightE
