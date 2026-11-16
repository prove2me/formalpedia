-- Prove2me | Theorems.Thm_MatchingNearLinear_Glauber_Supplement_star_spectral_gap
-- name    : MatchingNearLinear.Glauber.Supplement.star_spectral_gap
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:58:44.526812+00:00
-- url     : https://prove2.me/theorems/a7a95029-df70-4f03-b4ee-63766623d304
-- title:
--   Lemma 6.3 — Star spectral gap
-- statement:
--   Fix $\lambda_{\max}>0$. There is a constant $C>0$, depending only on $\lambda_{\max}$, such that the following holds. Let $G$ be a simple graph on $n\ge2$ vertices with $m\ge1$ edges and base activities $0<\lambda_e\le\lambda_{\max}$, and let $0<a\le1$. Write $\mu_a=\mu_{G,a\lambda}$ and $P=P^{G,a}_{\mathrm{star}}$ for ordinary star Glauber dynamics. Then for every real function $f$ on matchings,
--   $$\operatorname{Var}_{\mu_a}(f)\ \le\ C\,n\log^2 n\;\mathcal E_P(f,f),\qquad \mathcal E_P(f,f)=\tfrac12\sum_{M,M'}\mu_a(M)P(M,M')\big(f(M)-f(M')\big)^2 .$$
--   Equivalently $T_{\mathrm{rel}}(P^{G,a}_{\mathrm{star}})=O_{\lambda_{\max}}(n\log^2n)$, uniformly over $0<a\le1$.
--
--   This is the spectral input of the weak Poincaré inequality behind the fast approximate counting algorithm.
--
--   Differences from the source:
--
--   - encoding: T_rel(P_star^{G,a}) = O_{λmax}(n log² n) uniformly over 0 < a ≤ 1 → Var_{μ_a}(f) ≤ C·n·(log n)²·E_P(f,f) for every f, with C chosen from λmax alone before n, G, λ and a; reason: T_rel = 1/gap and the Poincaré inequality with constant T_rel are equivalent for a reversible kernel; the inequality form needs no inverse
-- source:
--   Tianshun Miao, Yitong Yin, Sampling Matchings in Near-linear Time, STOC 2027 submission #444 (October 2026), Lemma 6.3 and Eq. (36), printed p. 29 (PDF p. 31); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/444.pdf

import Mathlib
import Definitions.Def_MatchingNearLinear_Glauber_Supplement_StarKernel

set_option autoImplicit false

namespace MatchingNearLinear.Glauber.Supplement

open MatchingNearLinear.Glauber

/-- Tianshun Miao and Yitong Yin, Sampling Matchings in Near-linear Time,
STOC 2027 submission #444 (October 2026). Exact result and pages in the item metadata. -/
theorem star_spectral_gap :
    ∀ lmax : ℝ, 0 < lmax → ∃ C : ℝ, 0 < C ∧
      ∀ (n m : ℕ), 2 ≤ n → 1 ≤ m → ∀ (G : Input n m) (lam : Fin m → ℝ), ActivityBound lam lmax →
      ∀ a : ℝ, 0 < a → a ≤ 1 → ∀ f : Config m → ℝ,
        variance (matchingLaw G (fun e => a * lam e)) f ≤
          C * n * (Real.log n)^2 *
            energy (matchingLaw G (fun e => a * lam e)) (starKernel G lam a) f f := by sorry

end MatchingNearLinear.Glauber.Supplement
