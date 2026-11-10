-- Prove2me | Theorems.Thm_NearOptOWF_theorem_3_2
-- name    : NearOptOWF.theorem_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:51:51.82837+00:00
-- url     : https://prove2.me/theorems/e6b003df-280d-4b5a-8ec7-14c254277847
-- title:
--   Theorem 3.2 — set lower-bound protocol: nmCAPP has an Arthur–Merlin protocol running in time $\epsilon^{-2}\cdot\mathrm{poly}(n)\cdot|C|$ (Goldwasser–Sipser)
-- statement:
--   **nmCAPP** (Definition 3.1) is the promise problem: given a non-deterministic circuit $C : \{0,1\}^n \times \{0,1\}^w \to \{0,1\}$, a $\beta \in [2^n]$ and $1/\epsilon = k \in \mathbb N$, accept if $\Pr_x[C(x) = 1] \ge (1+\epsilon)\beta/2^n$ and reject if $\Pr_x[C(x) = 1] < \beta/2^n$.
--
--   There is a polynomial $p$ such that nmCAPP has an Arthur–Merlin protocol (one round, public coin, completeness $2/3$, soundness $1/3$) whose verifier time, verifier randomness, verifier communication and prover communication are all at most
--   $$
--   (k+1)^2 \cdot p\bigl(n + w + |C| + \log \beta\bigr).
--   $$
--
--   This is the tool that turns the gap between Claims 4.8 and 4.9 into an AM protocol certifying $\varphi \notin \mathrm{SAT}$.
--
--   Differences from the source:
--   - reading: "runs in time ε^{-2} · poly(n) · |C|" → verifier time, randomness and communication ≤ (k + 1)² · p(n + w + |C| + log β), k = 1/ε; reason: the paper fixes no machine model; on the published one-tape machines reading the circuit code takes Θ(|C| log |C|), so |C| is read polynomially; ε^{-2} is kept ((k + 1)² ≤ 4k²); log β ≤ n + 1 on instances and lets the verifier read malformed tuples
--   - reading: "an Arthur-Merlin protocol" → a one-round public-coin interactive proof (published LaconicBarrier.InAM) with completeness 2/3 and soundness 1/3; reason: the standard AM; constant-round AM collapses to one round
--   - encoding: the instance (C, β, 1/ε) → the tuple (1ⁿ, 1^w, code of C, β in binary, 1^k), with β ∈ [2ⁿ] and k ≥ 1 part of the yes and no sets; reason: an injective encoding; tuples violating the promise are in neither set
-- source:
--   Ilango–Lombardi–Tu, Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), Theorem 3.2, p.8 (PDF p.10); Definition 3.1, same page

import Mathlib
import Definitions.Def_NearOptOWF_nmCAPPYes
import Definitions.Def_NearOptOWF_nmCAPPNo
import Definitions.Def_NearOptOWF_NmCAPPInst_enc
import Definitions.Def_LaconicBarrier_InIP

namespace NearOptOWF

/-- **Theorem 3.2 (set lower-bound protocol, Goldwasser–Sipser [GS89])** (Ilango–Lombardi–Tu, *Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP*, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), Theorem 3.2, p.8
(PDF p.10); nmCAPP is Definition 3.1, same page): there is an Arthur–Merlin protocol for nmCAPP that
runs in time `ε^{−2} · poly(n) · |C|`. Formally: there is a polynomial `p` such that nmCAPP has a
one-round public-coin interactive proof (the published `LaconicBarrier.InAM`) with completeness
`2/3`, soundness `1/3`, and verifier time, verifier randomness, verifier communication and prover
communication all at most `(k + 1)² · p(n + w + |C| + log β)`, where `k = 1/ε`.

**Formalization Note** The linear factor `|C|` is read as a polynomial in `(n, w, |C|)`: the paper fixes
no machine model, and on the published one-tape machines reading the circuit code already takes
`Θ(|C| log |C|)` steps. The factor `ε^{−2} = k²` is kept, as `(k + 1)² ≤ 4k²` for `k ≥ 1`. The term
`log β` (`β`'s binary length, at most `n + 1` on instances) lets the verifier read malformed tuples. -/
theorem theorem_3_2 : ∃ p : Polynomial ℕ,
    LaconicBarrier.InAM NmCAPPInst.enc nmCAPPYes nmCAPPNo 1
      (fun I => (I.k + 1) ^ 2 * p.eval (I.n + I.w + I.C.gates.length + Nat.size I.β))
      (fun I => (I.k + 1) ^ 2 * p.eval (I.n + I.w + I.C.gates.length + Nat.size I.β))
      (fun I => (I.k + 1) ^ 2 * p.eval (I.n + I.w + I.C.gates.length + Nat.size I.β))
      (fun I => (I.k + 1) ^ 2 * p.eval (I.n + I.w + I.C.gates.length + Nat.size I.β))
      (fun _ => 1 / 3) (fun _ => 1 / 3) := by sorry

end NearOptOWF
