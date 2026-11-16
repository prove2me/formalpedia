-- Prove2me | Theorems.Thm_KTCenter_Supplement_theorem_5_1
-- name    : KTCenter.Supplement.theorem_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:07:10.07382+00:00
-- url     : https://prove2.me/theorems/e1d0ce38-4362-42db-bb4d-293a1339cd9e
-- title:
--   Theorem 5.1 — a randomized $(1+\varepsilon)$-approximate Kendall–tau center with probability $\ge 4/5$ in time $(nd+1)^{O_\varepsilon(1)}$
-- statement:
--   Let $\Pi=(\pi_1,\dots,\pi_n)$ be a list of $n\ge1$ complete rankings of $d\ge1$ candidates, let $\mathcal K$ be the Kendall–tau distance, $\mathrm{Obj}(\Pi,\sigma)=\max_{i\in[n]}\mathcal K(\sigma,\pi_i)$ the radius of a ranking $\sigma$, and $R^*=\min_\sigma\mathrm{Obj}(\Pi,\sigma)$ the optimal radius.
--
--   For every fixed real $\varepsilon>0$ there is a randomized algorithm and a constant $c=c(\varepsilon)$ such that, on every input $\Pi$:
--
--   1. on every string of coins the algorithm halts within $(nd+1)^c$ steps, uses at most $(nd+1)^c$ coins, and returns a complete ranking $\hat\sigma$;
--   2. with probability at least $4/5$ over fair coins,
--   $$\mathrm{Obj}(\Pi,\hat\sigma)\le(1+\varepsilon)R^*.$$
--
--   This is the randomized approximation scheme of §5; the paper's main result (Theorem 1.1) removes the randomness via §6.
--
--   **Formalization Note** The algorithm is one Mathlib `Turing.TM2ComputableInPolyTime` machine over the four-letter alphabet, reading the coin string, a separator and the binary encoding of $\Pi$, and writing the one-line form of $\hat\sigma$ (1-based labels). The number of coins is a fixed polynomial of the input length, so the coin length carries no information beyond the input length. $\varepsilon$ is not an input; $c$ is chosen after $\varepsilon$ and before $\Pi$.
--
--   Differences from the source:
--
--   - reading: "a randomized algorithm" and "runs in time (nd + 1)^{O_ε(1)} on every execution" → a TM2 machine on (coin string, binary encoding of Π) whose number of coins is a polynomial in the input length, with coin length and running time ≤ (nd + 1)^c on every coin string, c depending only on ε; reason: the paper names no machine, counts binary encoding length, and implements its draws with fair bits (Remark 5.14)
--   - reading: "with probability at least 4/5" → the fraction of coin strings of the fixed length on which the output satisfies the bound is ≥ 4/5; reason: probability over fair coins, as in Remark 5.14, which already accounts for the finite-bit loss
--   - reading: "returns a complete ranking σ̂ satisfying … with probability at least 4/5" → the output is a complete ranking on every coin string, and the radius bound holds with probability ≥ 4/5; reason: the stronger of the two readings, and the one Algorithm 10 satisfies (it always returns σ_best)
--   - reading: "For every fixed ε > 0" → ∀ real ε > 0, then the machine and c; ε is not an input; reason: one algorithm per fixed ε, as stated
--   - encoding: a set Π = {π₁, …, π_n} → a list Fin n → Perm (Fin d), repeats allowed; reason: the paper itself uses "the input list" (p.13); a list covers every set
--   - encoding: output ranking σ̂ → its one-line form as 1-based labels; reason: Lean convention; determines σ̂
-- source:
--   Chakraborty, Das, Mukherjee, Kendall–tau Center Admits a PTAS, STOC 2027 submission (manuscript sha256 4739ffba…), Theorem 5.1, p.22 (PDF p.24); Remark 5.14, p.55 (PDF p.57)

import Mathlib
import Definitions.Def_KTCenter_Instance
import Definitions.Def_KTCenter_encInstance
import Definitions.Def_KTCenter_Supplement_coinFrac

namespace KTCenter.Supplement

/-- **Theorem 5.1** (Randomized Kendall–tau PTAS), p.22 (PDF p.24).

Chakraborty, Das, Mukherjee, *Kendall–tau Center Admits a PTAS*, STOC 2027 submission (manuscript
sha256 4739ffba…).

**Formalization Note.** A randomized algorithm is one Mathlib `Turing.TM2ComputableInPolyTime`
machine reading `encPair encInstance (I, b)`: a coin string `b` and the binary encoding of the
input list. The number of coins is `L(|enc I|)` for a polynomial `L` (no advice in the coin length).
`ε` is real, precedes the machine and is not an input; one exponent `c`, chosen after `ε` and before
the input, bounds both the coin length and the running time on every coin string ("on every
execution"). The machine always outputs the one-line form of a complete ranking, and the output
ranking has radius at most `(1 + ε)R*` on at least `4/5` of the coin strings (`coinFrac`). -/
theorem theorem_5_1 (ε : ℝ) (hε : 0 < ε) :
    ∃ alg : Instance × List Bool → List ℕ,
      ∃ h : Turing.TM2ComputableInPolyTime (encPair encInstance) encRanking alg,
      ∃ L : Polynomial ℕ,
        (∃ c : ℕ, ∀ I : Instance,
          L.eval (encInstance I).length ≤ (I.n * I.d + 1) ^ c ∧
          ∀ b : Fin (L.eval (encInstance I).length) → Bool,
            h.time.eval (encPair encInstance (I, List.ofFn b)).length ≤ (I.n * I.d + 1) ^ c) ∧
        ∀ I : Instance,
          (∀ b : Fin (L.eval (encInstance I).length) → Bool,
            ∃ σ : Equiv.Perm (Fin I.d), alg (I, List.ofFn b) = rankingList σ) ∧
          (4 / 5 : ℚ) ≤ coinFrac alg (L.eval (encInstance I).length) I
            (fun out => ∃ σ : Equiv.Perm (Fin I.d),
              out = rankingList σ ∧ (obj I σ : ℝ) ≤ (1 + ε) * (optRadius I : ℝ)) := by sorry

end KTCenter.Supplement
