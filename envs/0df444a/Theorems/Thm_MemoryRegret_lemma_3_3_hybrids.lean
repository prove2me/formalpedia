-- Prove2me | Theorems.Thm_MemoryRegret_lemma_3_3_hybrids
-- name    : MemoryRegret.lemma_3_3_hybrids
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:40:41.911815+00:00
-- url     : https://prove2.me/theorems/42ced841-965e-4f49-8e91-7cd7ada536c3
-- title:
--   Lemma 3.3 — adjacent hybrids are indistinguishable
-- statement:
--   There are absolute constants $C>0$ and $K$ with the following property. Let $\mu$ be a distribution on a finite set $X$ and $H$ a finite nonempty class whose matrix is a $(k,\ell)$-$L_2$-extractor with error $2^{-r}$ with respect to $\mu$, with $0<\varepsilon<1/(10^3r)$ and $1\le m\le1/(10^6\varepsilon^2r^2)$. Let $B$ be a branching program over $X\times\{0,1\}^m$ of width at most $2^{Ck\ell/(\varepsilon r\sqrt m)}$ and length $T_{\mathrm{block}}\le2^{\min(k,\ell,r)/10}$. Then for every $t$ the distinguishing advantage of $B$ between $\mathcal D^t$ and $\mathcal D^{t+1}$ is at most $K\,2^{-\min(k,\ell,r)/5}$.
--
--   Summing over $t$ gives Theorem 4 by the hybrid argument.
--
--   Differences from the source:
--   - encoding: t ∈ {0, 1, …, T_block} → t < T_block; reason: 𝒟^{t+1} is defined only for t + 1 ≤ T_block
--   - encoding: width 2^{Ckℓ/εr√m} for a sufficiently small constant C, and O(·) → ∃ C > 0, ∃ K before all parameters; width at most the stated value; reason: the standard meaning
--   - encoding: k, ℓ, r sufficiently large (the source relies on Proposition 5 and the assumptions of §3.3) → no threshold stated; ε ≤ ½ is written out; reason: below any threshold on min(k, ℓ, r) the bound holds with a larger K because an advantage is at most 1; ε·10³r < 1 does not bound ε for small r, and ε ≤ ½ excludes only undefined cases
--   - encoding: B a branching program (randomness fixed without loss of generality, p.12) → a deterministic program; reason: the randomized case follows by averaging over the seed
--   - encoding: ε < 1/(10³r) and m ≤ 1/(10⁶ε²r²) → ε·10³r < 1 and m·10⁶ε²r² ≤ 1; reason: multiplicative form avoids x/0 = 0; the same instances for r > 0
--   - generalization: the class H ⊆ {0,1}^X with h uniform on H → an indexed family hyp : ι → X → Bool with i uniform on ι; reason: ι = H with hyp h = h is the source statement; the family form also covers the [d]-indexed matrix of Lemma 4.1 and allows repetitions
--   - encoding: branching program with at most d vertices per layer and width bound on d → one finite state type S per program, with width |S|; reason: a width-d program is the case S = Fin d
-- source:
--   Brukhim, Garg, Memory-Regret Tradeoffs for Online Learning (manuscript, sha256 89bb0279…), Lemma 3.3, p.13, under the assumptions of Theorem 4 (§3.2, p.12)

import Mathlib
import Definitions.Def_MemoryRegret_IsProbVec
import Definitions.Def_MemoryRegret_IsL2Extractor
import Definitions.Def_MemoryRegret_streamD1
import Definitions.Def_MemoryRegret_BranchingProgram

namespace MemoryRegret

/-- **Lemma 3.3 (adjacent hybrids are indistinguishable).**
Brukhim, Garg, *Memory-Regret Tradeoffs for Online Learning* (manuscript, sha256 89bb0279…),
Lemma 3.3, p.13, under the assumptions of Theorem 4 (§3.2).

There are absolute constants `C > 0` and `K` such that: let `µ` be a distribution on a finite
`X`, `(hyp i)_{i∈ι}` a finite nonempty class whose matrix is a `(k, ℓ)`-L2-extractor with error
`2^{−r}` w.r.t. `µ`, `0 < ε < 1/(10³r)` and `1 ≤ m ≤ 1/(10⁶ε²r²)`. Every branching program `B`
over `X × {0,1}^m` of width at most `2^{Ckℓ/(εr√m)}` and length `T_block ≤ 2^{min(k,ℓ,r)/10}`
has, for every `t`, distinguishing advantage between the hybrids `𝒟^t` and `𝒟^{t+1}` at most
`K·2^{−min(k,ℓ,r)/5}`.

**Formalization Note.** "For any t ∈ {0, 1, …, T_block}" is `t < T_block`, the range in which
`𝒟^{t+1}` is defined. "A sufficiently small constant C" and `O(·)` are `∃ C > 0, ∃ K` before all
parameters. The advantage is `|Pr_{𝒟^t}[YES] − Pr_{𝒟^{t+1}}[YES]|` for a deterministic program;
by averaging this covers randomized ones. Ratios are written multiplicatively. `ε ≤ ½` is
explicit because `ε·10³r < 1` does not bound `ε` for small `r`, where `Ber(·, ½ + ε)` would not be
a distribution; it excludes only undefined cases (for `r ≥ 1/500` it is implied). No
"sufficiently large" threshold is stated: below any threshold on `min(k,ℓ,r)` the bound holds
with a larger `K`, since a distinguishing advantage is at most `1`. -/
theorem lemma_3_3_hybrids :
    ∃ C : ℝ, 0 < C ∧ ∃ K : ℝ, ∀ (X : Type) [Fintype X] (μ : X → ℝ), IsProbVec μ →
      ∀ (ι : Type) [Fintype ι] [Nonempty ι] (hyp : ι → X → Bool) (k ℓ r ε : ℝ) (m Tb : ℕ)
        (S : Type) [Fintype S] (B : BranchingProgram S (X × (Fin m → Bool)) Tb),
        IsL2Extractor μ hyp k ℓ r → 0 < ε → ε ≤ 1 / 2 → ε * (10 ^ 3 * r) < 1 → 1 ≤ m →
        (m : ℝ) * (10 ^ 6 * ε ^ 2 * r ^ 2) ≤ 1 →
        (Fintype.card S : ℝ) ≤ (2 : ℝ) ^ (C * k * ℓ / (ε * r * Real.sqrt m)) →
        (Tb : ℝ) ≤ (2 : ℝ) ^ (min k (min ℓ r) / 10) →
        ∀ t : ℕ, t < Tb →
          |B.outProb (hybridD μ hyp ε t) true - B.outProb (hybridD μ hyp ε (t + 1)) true| ≤
            K * (2 : ℝ) ^ (-(min k (min ℓ r) / 5)) := by sorry

end MemoryRegret
