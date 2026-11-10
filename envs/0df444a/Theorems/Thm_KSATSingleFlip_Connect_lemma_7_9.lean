-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_lemma_7_9
-- name    : KSATSingleFlip.Connect.lemma_7_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T21:07:50.082425+00:00
-- url     : https://prove2.me/theorems/6d503031-84eb-42ef-b1fb-bd18dedd47ea
-- title:
--   Lemma 7.9 — Hamming distance after the Glauber walk: $d_H(z,X_t)>8\ln(1/\rho)n/k$
-- statement:
--   Assume $m/n$ lies in (1.2), i.e. $m/n\le\frac{2^k}{k}(\ln k+\ln\ln k+\gamma^*-(\ln\ln k)^{-1/16})$. For fixed $z\in\{0,1\}^n$, sample $M\sim\mathrm{Pois}(m)$, $\Phi^+\sim\Phi(k,n,M)$, and let $(X_t)$ be Glauber dynamics on $\Phi_0 = \Phi^+[z]$ from $z$. With $N = T_kn$ for $T_k\in\mathbb N$ sufficiently large depending only on $k$: for every integer $t\ge N$, with probability at least $1-e^{-4\rho^{10}n}$, if $\mathsf{LT}(\Phi^+)$ holds then $d_H(z,X_t)>8\ln(1/\rho)\,n/k$.
--
--   In Lean, the degree cutoff of $\mathsf{LT}$ (the paper's $D_k$) is an arbitrary $D$ fixed after $k$, and $T_k$ is chosen after it; "sufficiently large $n$" follows the standing convention.
--
--   Differences from the source:
--   - generalization: LT with the paper's degree cutoff D_k (fixed in Lemma 7.6's proof); T_k sufficiently large depending only on k → ∀ D (any cutoff), ∃ T_k chosen after D; reason: for the paper's D_k this is the source statement, and T_k still depends only on k; the proof works for any cutoff (it uses D_k only through the ball-size bound B_k = M_{2k+4,D_k})
--   - reading: no explicit range of n → ∃ n₀, ∀ n ≥ n₀; reason: standing convention of p. 2 (the proof's last inequality is for large n)
--   - encoding: Glauber dynamics with uniform variable and uniform resampling among allowed values → glauberState with an update sequence uniform on (Fin n × Bool)^t; reason: same transition law (see the Glauber definition)
--   - encoding: M ∼ Pois(m) and then M independent clauses → poisExp/poisProb: the series ∑_M e^{-m} m^M/M! · (uniform average over M-tuples of clauses); reason: same law; the integrands lie in [0,1], so the series converges
--   - encoding: variables [n] = {1,…,n}, formulas as indexed clause collections → variables Fin n; Φ(k,n,m) = uniform law on the published Formula n k m; other formulas are clause lists (position = clause index), sub-formulas are sets of positions; reason: bijective reindexing; repeated clauses stay distinct, as in the paper's indexed collections
--   - encoding: m ≥ 0 is the mean of the Poisson clause count → m : ℝ with 0 ≤ m; reason: the law in Lemma 7.8 permits every nonnegative real mean, including zero; restricting it to natural means omits these instances
-- source:
--   Wang, Yin, Yu, Zhang (2026), Single-Variable Connectivity in Random k-SAT, arXiv:2611.05981 (held version, SHA-256 1821a501…58b80f5), Lemma 7.9, printed p. 58 (PDF 60)

import Mathlib
import Definitions.Def_SATComputability
import Definitions.Def_KSATSingleFlip_Connect_Model
import Definitions.Def_KSATSingleFlip_Connect_FactorGraph
import Definitions.Def_KSATSingleFlip_Connect_SoftField
import Definitions.Def_KSATSingleFlip_Connect_Glauber

open scoped Classical BigOperators
open OAI.FixedClauseThreshold

namespace KSATSingleFlip.Connect

/-- Lemma 7.9 (Hamming distance after the Glauber walk; printed p. 58). For `m/n` in (1.2), fixed
`z`, `M ∼ Pois(m)`, `Φ⁺ ∼ Φ(k, n, M)` and Glauber dynamics `(X_t)` on `Φ₀ = Φ⁺[z]` from `z` (uniform
update sequence), for every `t ≥ N = T_k n`: with probability at least `1 − e^{−4ρ^{10} n}`,
`LT(Φ⁺)` implies `d_H(z, X_t) > 8 ln(1/ρ) n/k`. `T_k` is chosen after the degree cutoff `D` of
`LT` (the paper's `D_k`); the statement is made for every value of the cutoff. -/
theorem lemma_7_9 :
    ∃ k0 : ℕ, ∀ k ≥ k0, ∀ D : ℕ, ∃ Tk : ℕ, ∃ n0 : ℕ, ∀ n ≥ n0, ∀ m : ℝ,
      0 ≤ m → m / n ≤ densityBound k gammaStar →
      ∀ (z : Fin n → Bool) (t : ℕ), Tk * n ≤ t →
        1 - Real.exp (-4 * rho k ^ 10 * n) ≤
          poisExp (allClauses n k) m (fun l =>
            uprob fun s : Fin t → Fin n × Bool =>
              LT k D (ofList l) →
                8 * Real.log (1 / rho k) * n / k <
                  (hamming z (glauberState (satBy (ofList l) z) z s) : ℝ)) := by sorry

end KSATSingleFlip.Connect
