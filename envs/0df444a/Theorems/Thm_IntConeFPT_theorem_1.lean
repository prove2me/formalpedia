-- Prove2me | Theorems.Thm_IntConeFPT_theorem_1
-- name    : IntConeFPT.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:44:29.807346+00:00
-- url     : https://prove2.me/theorems/edb39f60-2944-4d13-9c2e-c30a7b9c150e
-- title:
--   Theorem 1 — (♣) is solvable deterministically in time $2^{\tau\log(\tau+1)2^{O(d)}}\cdot|I|^{O(1)}$ with optimal certificates of at most $2^{2d+1}$ distinct generators per type
-- statement:
--   There are an absolute constant $C$ and a deterministic algorithm that, on every valid instance $I$ of (♣) (dimensions $d\ge1$, $k\ge0$, $\tau\ge1$ types, rational polytopes $P^{(t)}$, convex rational polynomial costs $f^{(t)}$ in dense encoding, rational polyhedra $Q$ and $\mathcal A$), halts within
--   $$
--   2^{\tau\log_2(\tau+1)\,2^{Cd}}\cdot|I|^{C}
--   $$
--   steps and
--
--   1. reports *infeasible* exactly when no feasible multiplicities exist; or
--   2. reports *unbounded* only when (♣) is unbounded below; or
--   3. returns an optimal aggregate $(y,v)=\sum_{t=1}^{\tau}(y^{(t)},v^{(t)})\in Q$ with $((y^{(t)},v^{(t)},N^{(t)}))_{t=1}^{\tau}\in\mathcal A$, together with a certificate consisting of rational generators and positive integer multiplicities, with at most $2^{2d+1}$ distinct generators per type, whose cost is at most that of every feasible representation (with real continuous coordinates).
--
--   This establishes fixed-parameter tractability of (♣) in $d+\tau$; the number $k$ of continuous coordinates, the coefficient sizes and the number of constraints enter only through $|I|$.
--
--   **Formalization Note** An algorithm is a Mathlib multi-stack Turing machine (`Turing.TM2ComputableAux`) over the alphabet $\{0,1,2,3\}$; numbers are written in binary (rationals in lowest terms) with the published encodings `encNat`, `encInt`, `encRat`, `encVec`, so the length of `encInstance I` is the paper's $|I|$ up to a constant factor. The constant $C$ is absolute and is chosen before the machine and before every input.
--
--   Differences from the source:
--   - encoding: deterministic algorithm with running time in terms of the binary input length |I| (no machine model named) → a Mathlib TM2 machine (`Machine`) over the alphabet Fin 4, step count bounded via `RunsWithin` on the binary encodings; reason: |I| is the binary input length and every input is rational, so the standard deterministic Turing model applies; a polynomial RAM-to-TM overhead is absorbed into the O(·) exponents
--   - encoding: O(·) in the time bound (and |I|^{O(1)} encoding-length bounds) → one absolute constant C : ℕ quantified before the machine and all inputs; logarithms to base 2; reason: for d ≥ 1 every O(d), O(d² log(d+1)) and O(1) is at most C times the displayed expression; the log base changes only C
--   - encoding: the algorithm runs on instances of (♣) (rational polytopes, convex polynomial costs) → correctness and the step bound are required on valid instances only (`Instance.Valid`); behaviour on other inputs is unconstrained; reason: the paper specifies its algorithm only on such instances; this changes no instance the paper speaks about
--   - encoding: types t ∈ [τ] = {1, …, τ} → t : Fin τ (0-based); reason: Lean convention; same instances
--   - reading: P^(1), …, P^(τ) (implicitly at least one type) → Instance.Valid requires 1 ≤ τ; reason: the paper lists τ types P^(1), …, P^(τ) and its bound contains log(τ + 1); there are no instances with τ = 0 in the source
--   - encoding: |I| includes the descriptions of all P^(t), f^(t) (dense encoding by total degree), Q and A → |I| = (encInstance I).length; reason: binary encoding with all sizes written out; equal to |I| up to a constant factor
--   - encoding: a certificate of rational generators and integer multiplicities, at most 2^{2d+1} distinct generators per type → lists of (x, u, μ) with x ∈ ℤ^d, u ∈ ℚ^k, μ ≥ 1, pairwise distinct (x, u), length ≤ 2^(2d+1) (CertOK); reason: a certificate is its support with positive multiplicities
-- source:
--   Jansen–Ohnesorge–Schumacher, A Constructive FPT Algorithm for Integer Cone Optimization with Convex Costs, arXiv:2609.31328 (preprint, sha256 9e28aed8…bc08a), Theorem 1, p.4

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_encNat
import Definitions.Def_OnlineCRS_Combine_encInt
import Definitions.Def_OnlineCRS_Combine_encRat
import Definitions.Def_OnlineCRS_Combine_encVec
import Definitions.Def_IntConeFPT_Machine
import Definitions.Def_IntConeFPT_Instance
import Definitions.Def_IntConeFPT_Problem
import Definitions.Def_IntConeFPT_Residue
import Definitions.Def_IntConeFPT_Formulation

open OnlineCRS.Combine

namespace IntConeFPT

/-- **Theorem 1.**
Jansen–Ohnesorge–Schumacher, *A Constructive FPT Algorithm for Integer Cone Optimization with
Convex Costs*, arXiv:2609.31328 (preprint), Theorem 1, p.4: "The problem (♣) can be solved deterministically
in time 2^{τ log(τ+1) 2^{O(d)}} · |I|^{O(1)}. The algorithm reports infeasibility or unboundedness
below, or returns an optimal aggregate (y, v) = Σ_{t=1}^τ (y^(t), v^(t)) ∈ Q satisfying
((y^(t), v^(t), N^(t)))_{t=1}^τ ∈ A, and a certificate consisting of rational generators and integer
multiplicities, with at most 2^{2d+1} distinct generators per type."

There are an absolute constant `C` and a deterministic Turing machine that, on every valid
instance `I` of (♣), halts within `2^{τ log₂(τ+1) 2^{C d}} · |I|^C` steps with a correct output
(`Output.Correct`): `infeasible` iff no feasible multiplicities exist; `unbounded` only if (♣) is
unbounded below; or an optimal aggregate with a certificate of rational generators and positive
integer multiplicities, at most `2^{2d+1}` distinct generators per type, optimal against every
feasible representation with real continuous coordinates.

**Formalization Note.** Machine model: `Machine`/`RunsWithin` (Mathlib TM2 over `Fin 4`);
`|I| = (encInstance I).length` (binary, dense polynomial encoding); `O(·)` as `fptBound`.
Validity (`d ≥ 1`, `τ ≥ 1`, bounded `P^(t)`, convex `f^(t)` on `P_x^(t)`) is the only hypothesis;
the cited algorithms ([GLS88], [Dad12], [VGZC20], [CGST86]) are part of the proof. -/
theorem theorem_1 :
    ∃ C : ℕ, ∃ M : Machine, ∀ I : Instance, I.Valid →
      ∃ o : Output I, o.Correct ∧
        RunsWithin M (encInstance I) (encOutput o) (fptBound C I.τ I.d (encInstance I).length) := by sorry

end IntConeFPT
