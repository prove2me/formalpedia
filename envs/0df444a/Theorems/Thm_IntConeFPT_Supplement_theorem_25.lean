-- Prove2me | Theorems.Thm_IntConeFPT_Supplement_theorem_25
-- name    : IntConeFPT.Supplement.theorem_25
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:26:13.121981+00:00
-- url     : https://prove2.me/theorems/86e01f57-c8f0-4f7a-8650-2a266b93091d
-- title:
--   Theorem 25 — additive schemes for $Q\|C_{\max}$ and $Q\|C_{\min}$ with per-machine error $\varepsilon p_{\max}/s_i$ in time $2^{\tau\log(\tau+1)2^{O(1/\varepsilon)}}\cdot|I|^{O(1)}$
-- statement:
--   Consider scheduling $n$ jobs with positive rational processing times $p_j$ on $m$ uniformly related machines with positive rational speeds $s_i$, where $\tau$ is the number of distinct speeds and $p_{\max}=\max_j p_j$. There is an absolute constant $C$ such that for every rational $\varepsilon\in(0,1]$ the following holds.
--
--   1. ($Q\|C_{\max}$) There is a deterministic algorithm that, on every instance $I$, runs in time
--   $$
--   2^{\tau\log_2(\tau+1)\,2^{C\lceil 1/\varepsilon\rceil}}\cdot|I|^{C}
--   $$
--   and returns a schedule $\sigma$ with
--   $$
--   C_i(\sigma)\le\mathrm{OPT}_{\max}+\frac{\varepsilon\,p_{\max}}{s_i}\qquad\text{for every machine } i,
--   $$
--   where $\mathrm{OPT}_{\max}$ is the minimum makespan over all schedules.
--   2. ($Q\|C_{\min}$) There is a deterministic algorithm with the same running time that returns a schedule $\sigma$ with
--   $$
--   C_i(\sigma)\ge\mathrm{OPT}_{\min}-\frac{\varepsilon\,p_{\max}}{s_i}\qquad\text{for every machine } i,
--   $$
--   where $\mathrm{OPT}_{\min}$ is the maximum over all schedules of the minimum completion load.
--
--   Since $s_i\ge s_{\min}$, both problems therefore admit an additive approximation scheme with error $\varepsilon p_{\max}/s_{\min}$, parameterized by $1/\varepsilon+\tau$.
--
--   **Formalization Note** An algorithm is a machine of the published `IntConeFPT_Machine` (Mathlib multi-stack Turing machine over $\{0,1,2,3\}$), and the time bound is its `fptBound` with $d=\lceil1/\varepsilon\rceil$. The constant $C$ is chosen before $\varepsilon$; each $\varepsilon$ has its own machine. $|I|$ is the length of the binary encoding of the instance.
--
--   Differences from the source:
--   - encoding: an algorithm running in time 2^{τ log(τ+1) 2^{O(1/ε)}} · |I|^{O(1)} (no machine model named) → a Mathlib TM2 machine (`IntConeFPT.Machine`) whose run on the encoded instance is bounded via `RunsWithin`; reason: the base mission's machine model; |I| is the binary input length, so the deterministic Turing model applies and a polynomial RAM-to-TM overhead is absorbed into the O(·) exponents
--   - encoding: O(1/ε) and O(1) in the time bound → one absolute constant C : ℕ, chosen before ε, with 2^{C⌈1/ε⌉} and |I|^C (fptBound C τ ⌈1/ε⌉₊ L); logarithm to base 2; reason: for ε ∈ (0,1], 1/ε ≤ ⌈1/ε⌉ ≤ 2/ε, so 2^{O(1/ε)} and 2^{C⌈1/ε⌉} agree up to the constant; the log base changes only C
--   - encoding: "for every rational ε there is an algorithm" → ∀ ε, ∃ M (one machine per ε, ε not part of the input); reason: the literal quantifier order of the statement
--   - encoding: n explicitly listed jobs and m machines, p_max = max_j p_j, s_min = min_i s_i → SchedInstance.Valid requires n ≥ 1, m ≥ 1 and positive p, s; reason: the source's instances; the maxima and minima are undefined otherwise
--   - encoding: jobs [n] and machines [m] → Fin n and Fin m (0-based); loads in ℝ on the cast rational data; reason: Lean convention; same instances
--   - encoding: the input instance and the returned schedule → encSched (n, m, p, s in binary, rationals in lowest terms) and encSchedule (σ(1), …, σ(n) in binary); |I| = (encSched I).length; reason: binary encoding of the explicit lists; equal to |I| up to a constant factor
-- source:
--   Jansen–Ohnesorge–Schumacher, A Constructive FPT Algorithm for Integer Cone Optimization with Convex Costs, arXiv:2609.31328 (preprint, sha256 9e28aed8…bc08a), Theorem 25, p.31

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

/-- **Theorem 25.**
Jansen–Ohnesorge–Schumacher, *A Constructive FPT Algorithm for Integer Cone Optimization with
Convex Costs*, arXiv:2609.31328 (preprint), Theorem 25, p.31: "For every rational ε ∈ (0, 1],
there is an algorithm running in time 2^{τ log(τ+1) 2^{O(1/ε)}} · |I|^{O(1)} that returns a
schedule with completion load at most OPT + εpmax/si on each machine i for Q||Cmax, and at least
OPT − εpmax/si for Q||Cmin."

There is an absolute constant `C` such that for every rational `ε ∈ (0,1]`:
(1) some machine, on every valid instance, halts within `2^{τ log₂(τ+1) 2^{C⌈1/ε⌉}} · |I|^C` steps
and outputs a schedule `σ` with `C_i(σ) ≤ OPT_max + ε p_max / s_i` for every machine `i`; and
(2) some machine, within the same bound, outputs a schedule with
`C_i(σ) ≥ OPT_min − ε p_max / s_i` for every machine `i`.

**Formalization Note.** Machine model `Machine`/`RunsWithin` and bound `fptBound` of the
published `IntConeFPT_Machine`, with `d := ⌈1/ε⌉₊` (for `ε ∈ (0,1]`, `1/ε ≤ ⌈1/ε⌉ ≤ 2/ε`, so
`2^{C⌈1/ε⌉}` and `2^{O(1/ε)}` agree up to `C`). `C` comes before `ε`; the machine may depend on
`ε` (one algorithm per `ε`). `τ = numSpeeds I`, `|I| = (encSched I).length`. -/
theorem theorem_25 :
    ∃ C : ℕ, ∀ ε : ℚ, 0 < ε → ε ≤ 1 →
      (∃ M : IntConeFPT.Machine, ∀ I : SchedInstance, I.Valid →
        ∃ σ : Fin I.n → Fin I.m,
          (∀ i, I.load σ i ≤ I.optMax + (ε : ℝ) * I.pmax / I.sR i) ∧
          IntConeFPT.RunsWithin M (encSched I) (encSchedule σ)
            (IntConeFPT.fptBound C I.numSpeeds ⌈1 / ε⌉₊ (encSched I).length)) ∧
      (∃ M : IntConeFPT.Machine, ∀ I : SchedInstance, I.Valid →
        ∃ σ : Fin I.n → Fin I.m,
          (∀ i, I.optMin - (ε : ℝ) * I.pmax / I.sR i ≤ I.load σ i) ∧
          IntConeFPT.RunsWithin M (encSched I) (encSchedule σ)
            (IntConeFPT.fptBound C I.numSpeeds ⌈1 / ε⌉₊ (encSched I).length)) := by sorry

end IntConeFPT.Supplement
