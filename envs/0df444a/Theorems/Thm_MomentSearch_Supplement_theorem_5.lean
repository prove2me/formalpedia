-- Prove2me | Theorems.Thm_MomentSearch_Supplement_theorem_5
-- name    : MomentSearch.Supplement.theorem_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T09:31:47.937263+00:00
-- url     : https://prove2.me/theorems/6cd27888-81dc-431c-8fdc-98746a7f26fa
-- title:
--   Theorem 5 — Coarse Greedy is an $O(1/\varepsilon)$-approximation on Kolmogorov balls of radius $n^{-\varepsilon}$
-- statement:
--   Search for a target on the path $[n]_0$, $n\ge2$, drawn from an unknown distribution $p$. There is an absolute constant $C>0$ with the following properties.
--
--   1. Let $\varepsilon\in(0,1]$, $\pi\in\Delta_n$, and let $U$ be a nonempty set with $U\subseteq B_K(\pi,n^{-\varepsilon})$. Let $S$ be Coarse Greedy run with nominal distribution $\pi$ and parameter $\varepsilon$, for any choice of $\pi$-medians. Then for every $p\in U$
--   $$\mathrm{cost}_p(S)\le\frac{C}{\varepsilon}\,\mathrm{OPT}(p),\qquad\text{i.e.}\qquad \sup_{p\in U}\frac{\mathrm{cost}_p(S)}{\mathrm{OPT}(p)}\le\frac C\varepsilon .$$
--   2. Consequently $\alpha(\mathcal U)\le C/\varepsilon$ for every collection $\mathcal U$ each of whose sets is contained in some Kolmogorov ball $B_K(\pi,n^{-\varepsilon})$ with $\pi\in\Delta_n$.
--   3. In particular $\alpha(\mathcal U_{K,n^{-\varepsilon}})\le C/\varepsilon$.
--
--   Here $\mathrm{cost}_p(S)=\sum_t p_t\,q(S,t)$ is the expected number of queries, $\mathrm{OPT}(p)$ its minimum over all deterministic strategies, and $\alpha$ the approximability factor of the base mission. An approximate CDF thus suffices for near-optimal search; Theorem 6 shows the factor $1/\varepsilon$ cannot be improved.
--
--   Differences from the source:
--   - encoding: sup_{p∈U} cost_p(S)/OPT(p) ≤ O(1/ε) → ∃ C > 0, chosen before n, ε, π, U, with cost_p(S) ≤ (C/ε)·OPT(p) for every p ∈ U; reason: OPT(p) ≥ 1 for n ≥ 2, so the ratio form and the product form agree; O(·) hides an absolute constant
--   - reading: the strategy obtained by running Coarse Greedy (the π-median queried is not specified) → for every median-selection rule med with IsMedianRule π med; reason: the paper fixes no median; the proof uses only the median property, so the statement for every rule is the paper's claim for each run of the algorithm
--   - reading: finishes by standard binary search on the remaining interval → binary search querying the middle vertex ⌊(a+b)/2⌋; reason: a standard binary search; the proof uses only its O(log n) worst-case depth
--   - generalization: α(𝒰) = O(1/ε) for an uncertainty collection 𝒰 (a collection covering Δ_n) each of whose sets lies in a Kolmogorov ball of radius n^{−ε} → for every collection 𝒰 of sets each contained in some B_K(π, n^{−ε}) with π ∈ Δ_n, covering or not; reason: the covering condition plays no role in the upper bound; covering collections are a special case
-- source:
--   Megow, Stein, Verschae, Distributionally Robust Search: The Power of Information and the Limits of Moments, arXiv:2611.04559 (held version, sha256 fbfa4b43350dfaea073a9c0a9a0850a9955ea82082a7163a2db90cc48b9339e3), Theorem 5, p.7 (PDF p.9); restated with proof App. A, p.17 (PDF p.19)

import Mathlib
import Definitions.Def_MomentSearch_OPT
import Definitions.Def_MomentSearch_approxFactor
import Definitions.Def_MomentSearch_Supplement_cdf
import Definitions.Def_MomentSearch_Supplement_coarseGreedy

open scoped ENNReal

namespace MomentSearch.Supplement

open MomentSearch

/-- **Theorem 5** (Distributionally robust search from approximate CDFs) (Megow, Stein, Verschae, *Distributionally Robust Search: The Power of Information and the Limits of Moments*, arXiv:2611.04559 (held version, sha256 fbfa4b43…), Theorem 5,
p.7 (PDF p.9); restated App. A, p.17 (PDF p.19)).

There is an absolute constant `C > 0` such that:
1. for `n ≥ 2`, `ε ∈ (0, 1]`, a nominal `π ∈ Δ_n` and a nonempty `U ⊆ B_K(π, n^{−ε})`, the
   strategy `S` obtained by running Coarse Greedy with nominal distribution `π` (for every
   choice of `π`-medians) satisfies `cost_p(S) ≤ (C/ε)·OPT(p)` for every `p ∈ U`, i.e.
   `sup_{p∈U} cost_p(S)/OPT(p) ≤ C/ε`;
2. consequently `α(𝒰) ≤ C/ε` whenever every set of `𝒰` is contained in a Kolmogorov ball of
   radius `n^{−ε}`;
3. in particular `α(𝒰_{K,n^{−ε}}) ≤ C/ε`.

**Formalization Note.** `O(1/ε)` is an absolute constant `C`, quantified before `n`, `ε`, `π`,
`U`. The supremum of ratios is written as `cost ≤ (C/ε)·OPT` for each `p ∈ U` (equivalent, as
`OPT(p) ≥ 1` for `n ≥ 2`). Clause 2 is stated for every collection, not only for collections
covering `Δ_n`. `log` is base 2. -/
theorem theorem_5 :
    ∃ C : ℝ, 0 < C ∧
      (∀ (n : ℕ), 2 ≤ n → ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        ∀ π ∈ stdSimplex ℝ (Fin n), ∀ U : Set (Fin n → ℝ), U.Nonempty →
          U ⊆ kolBall π ((n : ℝ) ^ (-ε)) →
          ∀ med : ℕ → ℕ → ℕ, IsMedianRule π med →
            ∀ p ∈ U, cost p (coarseGreedy π ε med) ≤ C / ε * OPT p) ∧
      (∀ (n : ℕ), 2 ≤ n → ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        ∀ 𝒰 : Set (Set (Fin n → ℝ)),
          (∀ U ∈ 𝒰, ∃ π ∈ stdSimplex ℝ (Fin n), U ⊆ kolBall π ((n : ℝ) ^ (-ε))) →
          approxFactor 𝒰 ≤ ENNReal.ofReal (C / ε)) ∧
      (∀ (n : ℕ), 2 ≤ n → ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        approxFactor (kolCollection n ((n : ℝ) ^ (-ε))) ≤ ENNReal.ofReal (C / ε)) := by sorry

end MomentSearch.Supplement
