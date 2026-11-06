-- Prove2me | Theorems.Thm_MinorityDynamics_lumping_2_1
-- name    : MinorityDynamics.lumping_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:16:56.096195+00:00
-- url     : https://prove2.me/theorems/b138ee0f-b58d-42bf-ab03-be8a2fff6ff6
-- title:
--   §2.1 and §8.1 — the minority count (with orientation) of k-Minority is a Markov chain with binomial transitions
-- statement:
--   Let $n$ and $k$ be odd. Consider one round of $k$-Minority.
--
--   1. **Without sources.** For every configuration $\omega$ with minority count $s$ and every $s'$,
--   $$\Pr\big(\text{the minority count after the round is } s'\big)=\Pr\big(\min\{Z,n-Z\}=s'\big),\qquad Z\sim\mathrm{Bin}\big(n,p(s/n)\big),$$
--   where $p(x)=\Pr(\mathrm{Bin}(k,x)\in\{1,\dots,\frac{k-1}2\}\cup\{k\})$ is (2.1).
--   2. **With sources.** Let $\mathrm{Src}$ be a set of $\varrho\ge1$ agents that all hold opinion $b$ in $\omega$, let $s$ be the minority count of $\omega$ and $\sigma$ its orientation ($\sigma=1$ iff $b$ is the minority opinion). Then for every $(s',\sigma')$, the probability that after the round the minority count is $s'$ and the orientation is $\sigma'$ equals the transition probability of the actual chain with sources: with $Z=\varrho\sigma+J$, $J\sim\mathrm{Bin}(n-\varrho,p(s/n))$, the probability that $\min\{Z,n-Z\}=s'$ and that the new orientation ($\sigma$ if $Z<n/2$, $1-\sigma$ if $Z>n/2$) is $\sigma'$.
--
--   This is the reduction from the agent-level process of Theorem 1.1 to the minority chain on which every lemma of the paper is stated.
--
--   Differences from the source:
--   - encoding: the law of X_{t+1} given X_t = x (a statement about the Markov chain of minority fractions) → for every configuration with minority count s, the one-round agent-level probability of each value of the lumped state equals the chain transition probability; reason: this is the lumpability that makes (X_t) a Markov chain with the stated transitions; same content
--   - encoding: agents sample k agents uniformly with replacement, independently → the array of all samples is uniform on {1..n}^{n×k}; reason: a uniform array has independent uniform entries; same law
-- source:
--   Giakkoupis, Los, Sauerwald, Ziccardi, Minority Dynamics with Small Samples, manuscript (STOC 2027 submission), §2.1, (2.1) and the display after it, pp.10–11; §8.1, "The actual chain", p.41

import Mathlib
import Definitions.Def_MinorityDynamics_Kernel
import Definitions.Def_MinorityDynamics_Agents
import Definitions.Def_MinorityDynamics_Chain

set_option autoImplicit false

open Classical

namespace MinorityDynamics

/-- **The minority count is a Markov chain with binomial transitions** (Giakkoupis, Los, Sauerwald, Ziccardi, *Minority Dynamics with Small Samples*, manuscript (STOC 2027 submission), §2.1, (2.1) and
the display after it, pp.10–11 = PDF pp.12–13; §8.1, "The actual chain", p.41 = PDF p.43):
"Given Xt = x, the probability that an agent adopts the current minority opinion is
p(x) = Pr(Bin(k, x) ∈ {1, . . . , (k−1)/2} ∪ {k}). … Given Xt = x, let Z count the agents holding
the current minority opinion after the next update. Then, Z ∼ Bin(n, p(x)), Xt+1 = min{Z, n − Z}/n."
With ϱ sources: "Z ∼ ϱσ + Bin(n − ϱ, p(x)), Xt+1 = min{Z, n − Z}/n, σt+1 = σ if Z < n/2, 1 − σ if
Z > n/2."

(a) Without sources: for every configuration `ω` with minority count `s`, the law of the minority
count after one round of k-Minority is the law of `min{Z, n − Z}`, `Z ∼ Bin(n, p(s/n))`.
(b) With a source set `Src` of `ϱ ≥ 1` agents all holding opinion `b`: for every such
configuration `ω`, the joint law of (minority count, orientation with respect to `b`) after one
round is the transition law of the actual chain with sources from (minority count of `ω`,
orientation of `ω`).

**Formalization Note** Both are exact identities of probability vectors: the probability of each
value of the lumped state after one agent-level round equals the chain's transition probability.
`n` and `k` are odd (p.2, p.10). -/
theorem lumping_2_1 (n k : ℕ) (hn : Odd n) (hk : Odd k) :
    (∀ (ω : Fin n → Bool) (s' : ℕ),
      ∑ ω' ∈ Finset.univ.filter (fun ω' : Fin n → Bool => minCount ω' = s'),
          agentStep n k ∅ ω ω' =
        foldedLaw n (pAdopt k ((minCount ω : ℝ) / n)) s') ∧
    (∀ (Src : Finset (Fin n)) (b : Bool) (ω : Fin n → Bool), 1 ≤ Src.card →
      (∀ i ∈ Src, ω i = b) → ∀ s : Fin (n + 1), (s : ℕ) = minCount ω →
      ∀ (s' : Fin (n + 1)) (σ' : Bool),
        ∑ ω' ∈ Finset.univ.filter
            (fun ω' : Fin n → Bool => minCount ω' = (s' : ℕ) ∧ orientation b ω' = σ'),
            agentStep n k Src ω ω' =
          sourceKernel n k Src.card (s, orientation b ω) (s', σ')) := by sorry

end MinorityDynamics
