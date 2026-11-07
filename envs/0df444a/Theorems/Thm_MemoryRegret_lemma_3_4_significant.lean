-- Prove2me | Theorems.Thm_MemoryRegret_lemma_3_4_significant
-- name    : MemoryRegret.lemma_3_4_significant
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:41:37.789878+00:00
-- url     : https://prove2.me/theorems/bf963baf-88fa-4b30-ad96-6b4fc58ac1ab
-- title:
--   Lemma 3.4 — the truncated path rarely reaches a significant vertex
-- statement:
--   There is an absolute constant $K$ with the following property. Let $\mu$ be a distribution on a finite set $X$ and $H$ a finite nonempty class whose matrix $M(x,h)=(-1)^{h(x)}$ is a $(k,\ell)$-$L_2$-extractor with error $2^{-r}$ with respect to $\mu$. Let $0<\varepsilon<1/(10^3r)$ and $1\le m\le1/(10^6\varepsilon^2r^2)$, and let $B$ be a branching program over $X\times\{0,1\}^m$ of width $d\le2^{k\ell/(10^4\varepsilon r\sqrt m)}$ and length $\tau\le2^{\min(r,k,\ell)/5}$. With $h$ uniform on $H$ and the $\tau$ samples i.i.d. from $D_h$,
--   $$\Pr[\mathcal T\text{ reaches a significant vertex}]\le K\,2^{-r'},\qquad r'=\min\Bigl(\frac r2,\frac k4,\frac\ell5\Bigr).$$
--
--   This is the technical heart of the memory lower bound: a low-memory program cannot learn much about the hidden hypothesis.
--
--   **Formalization Note** The truncated path is defined inductively (see `truncAlive`) with $\ell'=\ell/6$ and $r'$ as in eq. (10).
--
--   Differences from the source:
--   - encoding: O(2^{−r′}) → K·2^{−r′} with K absolute and quantified first; reason: the standard meaning
--   - encoding: k′, ℓ′ (and k, ℓ, r) sufficiently large, as assumed in §3.3–3.4 → no threshold stated; reason: equivalent: below any threshold on r′ the bound holds with a larger K because a probability is at most 1, and a large r′ makes k, ℓ, r, k′, ℓ′ large under the other hypotheses
--   - encoding: ε < 1/(10³r), with r sufficiently large → ε ≤ ½ is written out; reason: without a threshold ε·10³r < 1 does not bound ε for small r, where Ber(·, ½ + ε) is not a distribution; this excludes only undefined cases
--   - encoding: ε < 1/(10³r) and m ≤ 1/(10⁶ε²r²) → ε·10³r < 1 and m·10⁶ε²r² ≤ 1; reason: multiplicative form avoids x/0 = 0; the same instances for r > 0
--   - generalization: the class H ⊆ {0,1}^X with h uniform on H → an indexed family hyp : ι → X → Bool with i uniform on ι; reason: ι = H with hyp h = h is the source statement; the family form also covers the [d]-indexed matrix of Lemma 4.1 and allows repetitions
--   - encoding: branching program with at most d vertices per layer and width bound on d → one finite state type S per program, with width |S|; reason: a width-d program is the case S = Fin d
-- source:
--   Brukhim, Garg, Memory-Regret Tradeoffs for Online Learning (manuscript, sha256 89bb0279…), Lemma 3.4, p.18, under the standing assumptions of §3.3, p.17

import Mathlib
import Definitions.Def_MemoryRegret_IsProbVec
import Definitions.Def_MemoryRegret_IsL2Extractor
import Definitions.Def_MemoryRegret_streamD1
import Definitions.Def_MemoryRegret_BranchingProgram
import Definitions.Def_MemoryRegret_truncAlive

namespace MemoryRegret

/-- **Lemma 3.4 (the truncated path rarely reaches a significant vertex).**
Brukhim, Garg, *Memory-Regret Tradeoffs for Online Learning* (manuscript, sha256 89bb0279…),
Lemma 3.4, p.18, under the standing assumptions of §3.3, p.17.

There is an absolute constant `K` such that the following holds. Let `µ` be a distribution on a
finite `X`, `(hyp i)_{i∈ι}` a finite nonempty class whose matrix `M(x, i) = (−1)^{hyp i x}` is a
`(k, ℓ)`-L2-extractor with error `2^{−r}` w.r.t. `µ`, `0 < ε < 1/(10³r)`,
`1 ≤ m ≤ 1/(10⁶ε²r²)`, and `B` a branching program over `X × {0,1}^m` of width
`d ≤ 2^{kℓ/(10⁴ε·r√m)}` and length `τ ≤ 2^{min(r,k,ℓ)/5}`. With `h` uniform on `ι` and the `τ`
samples i.i.d. `D_h`, the probability that the truncated path `𝒯` reaches a significant vertex
is at most `K·2^{−r′}`, where `r′ = min(r/2, k/4, ℓ/5)` (eq. (10)).

**Formalization Note.** `O(2^{−r′})` is `K·2^{−r′}` with `K` absolute and chosen first. The
paper also assumes `k′, ℓ′` (and `k, ℓ, r`) "sufficiently large"; no threshold is stated
here, which is equivalent: below any fixed threshold on `r′` the bound holds with a larger `K`
(a probability is at most `1`), and a large `r′` makes `k′`, `ℓ′`, `k`, `ℓ`, `r` large under
the other hypotheses. `ε ≤ ½` is explicit because `ε·10³r < 1` does not bound `ε` for small `r`,
where `Ber(·, ½ + ε)` would not be a distribution; it excludes only undefined cases. The
truncated path is `truncAlive`, the event is `reachesSignificant`.
The ratios are written multiplicatively. -/
theorem lemma_3_4_significant :
    ∃ K : ℝ, ∀ (X : Type) [Fintype X] (μ : X → ℝ), IsProbVec μ →
      ∀ (ι : Type) [Fintype ι] [Nonempty ι] (hyp : ι → X → Bool) (k ℓ r ε : ℝ) (m τ : ℕ)
        (S : Type) [Fintype S] (B : BranchingProgram S (X × (Fin m → Bool)) τ),
        IsL2Extractor μ hyp k ℓ r → 0 < ε → ε ≤ 1 / 2 → ε * (10 ^ 3 * r) < 1 → 1 ≤ m →
        (m : ℝ) * (10 ^ 6 * ε ^ 2 * r ^ 2) ≤ 1 →
        (Fintype.card S : ℝ) ≤ (2 : ℝ) ^ (k * ℓ / (10 ^ 4 * ε * r * Real.sqrt m)) →
        (τ : ℝ) ≤ (2 : ℝ) ^ (min r (min k ℓ) / 5) →
        wprob (jointLaw μ hyp ε) (· ∈ reachesSignificant (jointLaw μ hyp ε) hyp B k ℓ r) ≤
          K * (2 : ℝ) ^ (-(min (r / 2) (min (k / 4) (ℓ / 5)))) := by sorry

end MemoryRegret
