-- Prove2me | Theorems.Thm_IntConeFPT_Supplement_theorem_26
-- name    : IntConeFPT.Supplement.theorem_26
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:26:44.602194+00:00
-- url     : https://prove2.me/theorems/2b2bb06d-9d75-47b3-b974-f0699dd767e9
-- title:
--   Theorem 26 — additive scheme for $Q\|C_{\mathrm{envy}}$ with error $\varepsilon p_{\max}/s_{\min}$ in time $2^{\tau\log(\tau+1)2^{O(1/\varepsilon)}}\cdot|I|^{O(1)}$
-- statement:
--   Consider scheduling $n$ jobs with positive rational processing times $p_j$ on $m$ uniformly related machines with positive rational speeds $s_i$, where $\tau$ is the number of distinct speeds, $p_{\max}=\max_j p_j$ and $s_{\min}=\min_i s_i$. For a schedule $\sigma$ let $C_i(\sigma)=\sum_{j\in\sigma^{-1}(i)}p_j/s_i$ be the completion load of machine $i$ and $E(\sigma)=\max_i C_i(\sigma)-\min_i C_i(\sigma)$ its envy, taken over all $m$ machines (empty machines have load $0$). Let $\mathrm{OPT}_{\mathrm{envy}}=\min_\sigma E(\sigma)$.
--
--   There is an absolute constant $C$ such that for every rational $\varepsilon\in(0,1]$ there is a deterministic algorithm that, on every instance $I$, runs in time
--   $$
--   2^{\tau\log_2(\tau+1)\,2^{C\lceil 1/\varepsilon\rceil}}\cdot|I|^{C}
--   $$
--   and returns a schedule $\sigma$ with
--   $$
--   E(\sigma)\le\mathrm{OPT}_{\mathrm{envy}}+\frac{\varepsilon\,p_{\max}}{s_{\min}}.
--   $$
--
--   Hence $Q\|C_{\mathrm{envy}}$ admits an additive approximation scheme with error $\varepsilon p_{\max}/s_{\min}$, parameterized by $1/\varepsilon+\tau$.
--
--   **Formalization Note** An algorithm is a machine of the published `IntConeFPT_Machine` (Mathlib multi-stack Turing machine over $\{0,1,2,3\}$), and the time bound is its `fptBound` with $d=\lceil1/\varepsilon\rceil$. The constant $C$ is chosen before $\varepsilon$; each $\varepsilon$ has its own machine. $|I|$ is the length of the binary encoding of the instance.
--
--   Differences from the source:
--   - reading: "the difference between the maximum and minimum load" → max_i C_i(σ) − min_i C_i(σ) with the completion loads C_i = Σ_{j∈σ⁻¹(i)} p_j/s_i over all m machines; reason: the proof of Theorem 26 (p.32) defines the load this way and writes E := max_i C_i − min_i C_i
--   - encoding: an algorithm running in time 2^{τ log(τ+1) 2^{O(1/ε)}} · |I|^{O(1)} (no machine model named) → a Mathlib TM2 machine (`IntConeFPT.Machine`) whose run on the encoded instance is bounded via `RunsWithin`; reason: the base mission's machine model; |I| is the binary input length, so the deterministic Turing model applies and a polynomial RAM-to-TM overhead is absorbed into the O(·) exponents
--   - encoding: O(1/ε) and O(1) in the time bound → one absolute constant C : ℕ, chosen before ε, with 2^{C⌈1/ε⌉} and |I|^C (fptBound C τ ⌈1/ε⌉₊ L); logarithm to base 2; reason: for ε ∈ (0,1], 1/ε ≤ ⌈1/ε⌉ ≤ 2/ε, so 2^{O(1/ε)} and 2^{C⌈1/ε⌉} agree up to the constant; the log base changes only C
--   - encoding: "for every rational ε there is an algorithm" → ∀ ε, ∃ M (one machine per ε, ε not part of the input); reason: the literal quantifier order of the statement
--   - encoding: n explicitly listed jobs and m machines, p_max = max_j p_j, s_min = min_i s_i → SchedInstance.Valid requires n ≥ 1, m ≥ 1 and positive p, s; reason: the source's instances; the maxima and minima are undefined otherwise
--   - encoding: jobs [n] and machines [m] → Fin n and Fin m (0-based); loads in ℝ on the cast rational data; reason: Lean convention; same instances
--   - encoding: the input instance and the returned schedule → encSched (n, m, p, s in binary, rationals in lowest terms) and encSchedule (σ(1), …, σ(n) in binary); |I| = (encSched I).length; reason: binary encoding of the explicit lists; equal to |I| up to a constant factor
-- source:
--   Jansen–Ohnesorge–Schumacher, A Constructive FPT Algorithm for Integer Cone Optimization with Convex Costs, arXiv:2609.31328 (preprint, sha256 9e28aed8…bc08a), Theorem 26, p.32

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_encNat
import Definitions.Def_OnlineCRS_Combine_encRat
import Definitions.Def_OnlineCRS_Combine_encVec
import Definitions.Def_HochbaumShmoys_Uniform_Packing
import Definitions.Def_IntConeFPT_Machine
import Definitions.Def_IntConeFPT_Supplement_Scheduling

open OnlineCRS.Combine

namespace IntConeFPT.Supplement

/-- **Theorem 26.**
Jansen–Ohnesorge–Schumacher, *A Constructive FPT Algorithm for Integer Cone Optimization with
Convex Costs*, arXiv:2609.31328 (preprint), Theorem 26, p.32: "For every rational ε ∈ (0, 1],
there is an algorithm running in time 2^{τ log(τ+1) 2^{O(1/ε)}} · |I|^{O(1)} that returns a
schedule with difference between the maximum and minimum load at most OPT + εpmax/smin."

There is an absolute constant `C` such that for every rational `ε ∈ (0,1]` some machine, on every
valid instance, halts within `2^{τ log₂(τ+1) 2^{C⌈1/ε⌉}} · |I|^C` steps and outputs a schedule `σ`
with `max_i C_i(σ) − min_i C_i(σ) ≤ OPT_envy + ε p_max / s_min`, where `C_i` is the completion
load (the proof's `C_i`, p.32) and all `m` machines count, empty ones with load `0`.

**Formalization Note.** As for `theorem_25`: `Machine`/`RunsWithin`/`fptBound` of the published
`IntConeFPT_Machine` with `d := ⌈1/ε⌉₊`, `C` before `ε`, one machine per `ε`,
`τ = numSpeeds I`, `|I| = (encSched I).length`. -/
theorem theorem_26 :
    ∃ C : ℕ, ∀ ε : ℚ, 0 < ε → ε ≤ 1 →
      ∃ M : IntConeFPT.Machine, ∀ I : SchedInstance, I.Valid →
        ∃ σ : Fin I.n → Fin I.m,
          I.envy σ ≤ I.optEnvy + (ε : ℝ) * I.pmax / I.smin ∧
          IntConeFPT.RunsWithin M (encSched I) (encSchedule σ)
            (IntConeFPT.fptBound C I.numSpeeds ⌈1 / ε⌉₊ (encSched I).length) := by sorry

end IntConeFPT.Supplement
