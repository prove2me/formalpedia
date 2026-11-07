-- Prove2me | Theorems.Thm_KTCenter_theorem_1_1
-- name    : KTCenter.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:28:21.79873+00:00
-- url     : https://prove2.me/theorems/79edd686-af1c-4440-a498-d0d7305dd75a
-- title:
--   Theorem 1.1 — a deterministic $(1+\varepsilon)$-approximate Kendall–tau center in time $(nd+1)^{O_\varepsilon(1)}$
-- statement:
--   For every fixed real $\varepsilon>0$ there is a deterministic algorithm that, given a list $\Pi=(\pi_1,\dots,\pi_n)$ of $n\ge1$ complete rankings on $d\ge1$ candidates, returns a complete ranking $\hat\sigma$ with
--
--   $$\max_{1\le i\le n}\mathcal K(\hat\sigma,\pi_i)\le(1+\varepsilon)R^*,\qquad R^*=\min_\sigma\max_{1\le i\le n}\mathcal K(\sigma,\pi_i),$$
--
--   and the algorithm runs in time $(nd+1)^{O_\varepsilon(1)}$.
--
--   Before this result only the trivial factor $2$ was known for an arbitrary number of inputs.
--
--   **Formalization Note** The algorithm is a Mathlib `Turing.TM2ComputableInPolyTime` machine over a four-letter alphabet, reading the binary encoding of the input list and writing the one-line form of $\hat\sigma$. The time bound is the explicit clause that the machine's step bound at the input length is at most $(nd+1)^c$, with $c$ chosen after $\varepsilon$ and before the input.
--
--   Differences from the source:
--
--   - reading: "a deterministic algorithm" and "runs in time (nd + 1)^{O_ε(1)}" → a TM2 machine computing the output from the binary encoding, with time polynomial ≤ (nd + 1)^c on every input, c depending only on ε; reason: the paper names no machine and counts binary encoding length (Theorems 5.13, 6.1)
--   - reading: "For every fixed ε > 0" → ∀ real ε > 0, then the machine and c; ε is not an input; reason: one algorithm per fixed ε, as stated
--   - encoding: a set Π = {π₁, …, π_n} → a list Fin n → Perm (Fin d), repeats allowed; reason: the paper itself uses "the input list" (p.13); a list covers every set
--   - encoding: output ranking σ̂ → its one-line form as 1-based labels; reason: Lean convention; determines σ̂
-- source:
--   Chakraborty, Das, Mukherjee, Kendall–tau Center Admits a PTAS, STOC 2027 submission (manuscript sha256 4739ffba…), Theorem 1.1, p.2 (PDF p.4)

import Mathlib
import Definitions.Def_KTCenter_Instance
import Definitions.Def_KTCenter_encInstance

namespace KTCenter

/-- **Theorem 1.1** (Kendall–tau center PTAS), p.2 (PDF p.4).

Chakraborty, Das, Mukherjee, *Kendall–tau Center Admits a PTAS*, STOC 2027 submission (manuscript
sha256 4739ffba…).

**Formalization Note.** The paper names no machine and counts in binary encoding length, so
"algorithm" and "time" are Mathlib's `Turing.TM2ComputableInPolyTime` over `OnlineCRS.Combine.Sym`.
`(nd + 1)^{O_ε(1)}` is the clause `h.time.eval |enc I| ≤ (nd + 1)^c`, with `c` chosen after `ε` and
before the instance. `ε` is real and is not an input: one machine for each `ε`. -/
theorem theorem_1_1 (ε : ℝ) (hε : 0 < ε) :
    ∃ alg : Instance → List ℕ,
      ∃ h : Turing.TM2ComputableInPolyTime encInstance encRanking alg,
        (∃ c : ℕ, ∀ I : Instance,
          h.time.eval (encInstance I).length ≤ (I.n * I.d + 1) ^ c) ∧
        ∀ I : Instance, ∃ σ : Equiv.Perm (Fin I.d),
          alg I = rankingList σ ∧ (obj I σ : ℝ) ≤ (1 + ε) * (optRadius I : ℝ) := by sorry

end KTCenter
