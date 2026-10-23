-- Prove2me | Theorems.Thm_LargeCongestion_Poisson_lemma_1_eq_21_corrected
-- name    : LargeCongestion.Poisson.lemma_1_eq_21_corrected
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:27:30.973975+00:00
-- url     : https://prove2.me/theorems/64b261ea-da00-4ce8-b0fd-eb8d6daa060b
-- title:
--   Lemma 1 (21), p. 18, corrected constant — |E[c_e(1 + Z_{i,e})] − c̆_e(x_e)| ≤ Λ̃(u) with ν e^{d_max} in Λ's first term (printed (21) is false)
-- statement:
--   Assume the costs are nonnegative and weakly increasing on $\mathbb N^*$ and the moment part of (18) holds with $\nu$ and $d_{\max} > 0$. Let $\Gamma_B$ be a Bernoulli congestion game with $d_{\mathrm{tot}} = \sum_i u_i \le d_{\max}$ and $u = \max_i u_i < 1$, let $\sigma$ be any mixed strategy profile, $X_e$ the random loads and $Z_{i,e} = X_e - U_{i,e}$ the loads excluding player $i$. Then $x_e = \mathsf E_\sigma[X_e]$ and $z_{i,e} = \mathsf E_\sigma[Z_{i,e}]$ satisfy $|z_{i,e} - x_e| = \mathsf E_\sigma[U_{i,e}] \le u$, and
--   $$\bigl|\mathsf E_\sigma[c_e(1 + Z_{i,e})] - \breve c_e(x_e)\bigr| \le \tilde\Lambda(u), \qquad \tilde\Lambda(u) = \frac{\nu\, d_{\max}\, e^{d_{\max}}}{2}\,\frac{u e^u}{(1-u)^2} + u\zeta .$$
--
--   A player's expected cost on a resource is uniformly close to the auxiliary cost at the expected load; since $\tilde\Lambda(u) \to 0$ as $u \to 0$, this is the step of Theorem 2 that passes the equilibrium inequalities to the limit.
--
--   **Formalization Note** *Corrected constant.* The paper's (21) has $\Lambda(u)$, with $\nu$ in place of $\nu e^{d_{\max}}$; that inequality is false (one resource, $c_e(j) = 403(j-2)^+$, $\nu = 1$, $d_{\max} = 6$, 300 players with $u_i = 1/100$: left side $4.1311$, $\Lambda(1/100) = 4.0552$; see the companion item `lemma_1_eq_21_printed_fails`). The paper's proof applies Theorem 9(b) with constant $\nu$, but Theorem 9(b) needs a bound on $\mathsf E[|\Delta^2 c_e(1+X)|]$ at $X \sim \mathrm{Poisson}(z_{i,e})$, and Proposition 5(a) gives only $e^{d_{\max} - z_{i,e}}\nu$. The page writes $\mathsf E_{\hat\sigma}$ in (21) for an arbitrary profile $\sigma$; it is read as $\mathsf E_\sigma$. The hypothesis $u < 1$ is added because $(1-u)^{-2}$ is $0$ in Lean at $u = 1$.
-- source:
--   Cominetti, Scarsini, Schröder & Stier-Moses, Approximation and Convergence of Large Atomic Congestion Games, arXiv:2001.02797v7, p. 18, Lemma 1 (second part), (19), (20), (21), corrected constant

import Mathlib
import Definitions.Def_TotalVariationDist
import Definitions.Def_LargeCongestion_Poisson_PoissonCalculus
import Definitions.Def_LargeCongestion_Poisson_Game

namespace LargeCongestion.Poisson

open MeasureTheory ProbabilityTheory

/-- Lemma 1, "Moreover" part, p. 18, with the **corrected constant**: for a Bernoulli congestion
game with `d_tot = ∑_i u_i ≤ d_max`, `u = max_i u_i < 1`, any mixed profile `σ`, player `i` and
resource `e`, the expectations `x_e = E_σ[X_e]`, `z_{i,e} = E_σ[Z_{i,e}]` satisfy
`|z_{i,e} − x_e| = E_σ[U_{i,e}] ≤ u` and `|E_σ[c_e(1 + Z_{i,e})] − c̆_e(x_e)| ≤ Λ̃(u)`, where
`Λ̃` is (20) with `ν e^{d_max}` in place of `ν`. The printed (21), with `Λ`, is false. -/
theorem lemma_1_eq_21_corrected {E T : Type*} [Fintype E] [DecidableEq E] [Fintype T]
    [DecidableEq T] (S : T → Finset (Finset E)) (c : E → ℕ → ℝ) (hc : IsCostFamily c)
    (ν dmax : ℝ) (hd : 0 < dmax) (hM : MomentBound c ν dmax) {N : ℕ} (τ : Fin N → T)
    (u : Fin N → ℝ) (hu : IsBernoulliGame u) (σ : Fin N → Finset E → ℝ)
    (hσ : IsMixedProfile S τ σ) (htot : ∑ i, u i ≤ dmax) (hu1 : maxU u < 1)
    (i : Fin N) (e : E) :
    |expect u σ (fun ω => (othersLoadRV i e ω : ℝ)) - expect u σ (fun ω => (loadRV e ω : ℝ))| =
        expect u σ (fun ω => (useIndicator i e ω : ℝ)) ∧
      expect u σ (fun ω => (useIndicator i e ω : ℝ)) ≤ maxU u ∧
      |expect u σ (fun ω => c e (1 + othersLoadRV i e ω)) -
          cBreve c e (expect u σ (fun ω => (loadRV e ω : ℝ)))| ≤ LamCorr c ν dmax (maxU u) := by sorry

end LargeCongestion.Poisson
