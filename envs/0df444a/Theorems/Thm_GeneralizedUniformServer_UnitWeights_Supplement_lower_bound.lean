-- Prove2me | Theorems.Thm_GeneralizedUniformServer_UnitWeights_Supplement_lower_bound
-- name    : GeneralizedUniformServer.UnitWeights.Supplement.lower_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-15T18:40:44.049745+00:00
-- url     : https://prove2.me/theorems/83cf5502-c7f3-47e4-bbaf-28439b9e4dac
-- title:
--   Theorem 1.2 — every randomized algorithm on $k$ copies of the uniform metric on $[k]$ has ratio at least $\frac1{20}k\ln k$
-- statement:
--   Consider generalized $k$-server on $k$ copies of the uniform metric on $k$ points: $M_1=\dots=M_k=[k]$ with unit distances, so configurations are $X=[k]^k$, moving from $x$ to $y$ costs the Hamming distance $d(x,y)$, and a request $r\in[k]^k$ is served by $x$ if $x_i=r_i$ for some $i$. A randomized online algorithm $A$ with start $a$ is **$\gamma$-competitive** if there is a constant $c$ with
--   $$\mathbb E[\mathrm{ALG}(\rho)]\le\gamma\cdot\mathrm{OPT}(\rho)+c\qquad\text{for every finite request sequence }\rho,$$
--   the expectation being over the algorithm's random choices for $\rho$ fixed in advance (oblivious adversary), and $\mathrm{OPT}(\rho)$ the optimal offline cost from $a$.
--
--   There is an absolute constant $k_0$ such that for every $k\ge k_0$, every start $a\in[k]^k$, every randomized online algorithm $A$ that serves every request, and all real $\gamma$, $c$: if $A$ is $\gamma$-competitive with additive constant $c$, then
--   $$\gamma\ge\frac1{20}\,k\ln k .$$
--
--   Together with Theorem 1.1 this shows that the randomized competitive ratio with unit distances is $\Theta(k\log k)$, lying between $\frac1{20}k\ln k$ and $(1+o(1))k\ln k$ for large $k$.
--
--   **Formalization Note** The algorithm ranges over the general history-dependent class (kernels seeing all earlier requests and the whole configuration history). The expected cost is computed in $[0,\infty]$ and compared as a real number; it is finite (at most $k\,|\rho|$), so the conversion loses nothing. The logarithm is natural (`Real.log`).
--
--   Differences from the source:
--   - encoding: competitive ratio at least (1/20) k ln k (infimum of the γ for which ALG is γ-competitive) → every γ admitting an additive constant c with E[ALG(ρ)] ≤ γ·OPT(ρ) + c for all ρ satisfies (1/20) k ln k ≤ γ; reason: an infimum is at least a bound iff every element is; an algorithm γ-competitive for no γ satisfies both vacuously.
--   - encoding: E[ALG(ρ)] as a real number → expected cost in ENNReal converted by toReal; reason: the expectation is finite (|ρ| steps of cost at most k), so the value is unchanged.
--   - encoding: all randomized online algorithms on k copies of the k-point uniform space → history-dependent PMF kernels on configurations (Fin k → Fin k), serving on every history; reason: conditional transition laws on this finite configuration space represent hidden memory and mixed strategies; unreachable histories can be filled by returning the current request, and relabeling points preserves costs.
-- source:
--   Junho Hwang, STOC 2027 submission #428 (October 2026), p. 3, Theorem 1.2 (proof §4, pp. 10–16; competitiveness defined on p. 8)

import Mathlib
import Definitions.Def_GeneralizedUniformServer_UnitWeights_Supplement_Online

namespace GeneralizedUniformServer.UnitWeights.Supplement

/-- Theorem 1.2 (source p. 3): there is an absolute constant `k₀` such that, for every `k ≥ k₀`,
every randomized online algorithm for generalized `k`-server on `k` copies of the uniform metric
on `k` points (`X = [k]^k`, unit distances, tuple requests) has competitive ratio at least
`(1/20) k ln k` against an oblivious adversary: whenever, from a start `a`, it satisfies
`E[ALG(ρ)] ≤ γ · OPT(ρ) + c` for every finite request sequence `ρ`, then `γ ≥ (1/20) k ln k`. -/
theorem lower_bound :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      ∀ (a : Config (fun _ : Fin k => Fin k))
        (A : GenOnlineAlg (fun _ : Fin k => Fin k) (Config (fun _ : Fin k => Fin k))),
        IsServing Serves A →
        ∀ γ c : ℝ,
          (∀ ρ : List (Config (fun _ : Fin k => Fin k)),
            (genExpectedCost A a ρ).toReal ≤ γ * (optCost a ρ : ℝ) + c) →
          (1 / 20 : ℝ) * (k : ℝ) * Real.log (k : ℝ) ≤ γ := by sorry

end GeneralizedUniformServer.UnitWeights.Supplement
