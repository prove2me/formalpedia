-- Prove2me | Theorems.Thm_MemoryRegret_theorem_4_distinguishing
-- name    : MemoryRegret.theorem_4_distinguishing
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:40:22.657226+00:00
-- url     : https://prove2.me/theorems/36f49c4e-45ba-46c8-995c-a349ec1987d0
-- title:
--   Theorem 4 — distinguishing needs memory
-- statement:
--   There is an absolute constant $c>0$ such that for every advantage $a>0$ there is $R_0$ with the following property. Let $\mu$ be a distribution on a finite set $X$ and $H$ a finite nonempty class whose matrix is a $(k,\ell)$-$L_2$-extractor with error $2^{-r}$ with respect to $\mu$, with $k,\ell,r\ge R_0$, and let $0<\varepsilon<1/(10^3r)$ and $1\le m\le1/(10^6\varepsilon^2r^2)$. Then every randomized streaming algorithm for distinguishing $\mathcal D_0$ from $\mathcal D_1$ (Definition 3) with memory at most $c\,k\ell/(\varepsilon r\sqrt m)$ bits and with $T_{\mathrm{block}}\le2^{\min(k,\ell,r)/10}$ elements has advantage less than $a$.
--
--   Equivalently, any streaming algorithm that distinguishes with constant advantage uses $\Omega(k\ell/(\varepsilon r\sqrt m))$ memory or more than $2^{\min(k,\ell,r)/10}$ elements. In particular the lower bound holds for a stream whose blocks carry only a tiny amount of information about the hidden hypothesis.
--
--   Differences from the source:
--   - reading: any streaming algorithm that distinguishes with constant advantage must use either Ω(kℓ/(εr√m)) memory or T_block > 2^{min(k,ℓ,r)/10} → the contrapositive with c absolute and quantified first, and R₀ depending on the advantage a, for randomized branching programs of width at most 2^{c·kℓ/(εr√m)}; reason: the hybrid proof gives c independent of a; large k, ℓ, r are needed for constant-advantage statements, and Theorem 11 supplies a randomized distinguisher
--   - encoding: ε < 1/(10³r) and m ≤ 1/(10⁶ε²r²) → ε·10³r < 1 and m·10⁶ε²r² ≤ 1; reason: multiplicative form avoids x/0 = 0; the same instances for r > 0
--   - generalization: the class H ⊆ {0,1}^X with h uniform on H → an indexed family hyp : ι → X → Bool with i uniform on ι; reason: ι = H with hyp h = h is the source statement; the family form also covers the [d]-indexed matrix of Lemma 4.1 and allows repetitions
--   - encoding: branching program with at most d vertices per layer and width bound on d → one finite state type S per program, with width |S|; reason: a width-d program is the case S = Fin d
-- source:
--   Brukhim, Garg, Memory-Regret Tradeoffs for Online Learning (manuscript, sha256 89bb0279…), Theorem 4, p.9

import Mathlib
import Definitions.Def_MemoryRegret_IsProbVec
import Definitions.Def_MemoryRegret_IsL2Extractor
import Definitions.Def_MemoryRegret_streamD1
import Definitions.Def_MemoryRegret_BranchingProgram

namespace MemoryRegret

/-- **Theorem 4 (distinguishing needs memory).**
Brukhim, Garg, *Memory-Regret Tradeoffs for Online Learning* (manuscript, sha256 89bb0279…),
Theorem 4, p.9.

There is an absolute constant `c > 0` such that for every advantage `a > 0` there is `R₀` with
the following property. Let `µ` be a distribution on a finite `X` and `(hyp i)_{i∈ι}` a finite
nonempty class whose matrix is a `(k, ℓ)`-L2-extractor with error `2^{−r}` w.r.t. `µ`, with
`k, ℓ, r ≥ R₀`; let `0 < ε < 1/(10³r)` and `1 ≤ m ≤ 1/(10⁶ε²r²)`. Then every (randomized)
streaming algorithm for the problem of distinguishing `𝒟_0` from `𝒟_1` (Definition 3) whose
memory is below `c·kℓ/(εr√m)` bits (width at most `2^{c·kℓ/(εr√m)}`) and that reads
`T_block ≤ 2^{min(k,ℓ,r)/10}` elements has advantage less than `a`.

**Formalization Note.** This is the contrapositive of "any streaming algorithm that
distinguishes … with constant advantage, must use either Ω(kℓ/(εr√m)) memory or
T_block > 2^{min(k,ℓ,r)/10}": the hidden constant `c` is absolute and chosen first, and the
asymptotics in `k, ℓ, r` are `∃ R₀` after the advantage. A streaming algorithm is a randomized
branching program (a seed distribution over deterministic programs of the same width). Ratios
are written multiplicatively. -/
theorem theorem_4_distinguishing :
    ∃ c : ℝ, 0 < c ∧ ∀ a : ℝ, 0 < a → ∃ R₀ : ℝ,
      ∀ (X : Type) [Fintype X] (μ : X → ℝ), IsProbVec μ →
      ∀ (ι : Type) [Fintype ι] [Nonempty ι] (hyp : ι → X → Bool) (k ℓ r ε : ℝ) (m Tb : ℕ),
        R₀ ≤ k → R₀ ≤ ℓ → R₀ ≤ r → IsL2Extractor μ hyp k ℓ r → 0 < ε →
        ε * (10 ^ 3 * r) < 1 → 1 ≤ m → (m : ℝ) * (10 ^ 6 * ε ^ 2 * r ^ 2) ≤ 1 →
        ∀ (S Ω : Type) [Fintype S] [Fintype Ω] (P : RandBP S (X × (Fin m → Bool)) Tb Ω),
          (Fintype.card S : ℝ) ≤ (2 : ℝ) ^ (c * k * ℓ / (ε * r * Real.sqrt m)) →
          (Tb : ℝ) ≤ (2 : ℝ) ^ (min k (min ℓ r) / 10) →
          P.advantage (streamD0 μ ε) (streamD1 μ hyp ε) < a := by sorry

end MemoryRegret
